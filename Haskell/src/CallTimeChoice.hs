{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module CallTimeChoice where
import           Base
import           Data.List                (delete)
import           Debug.Trace
import           Prelude                  hiding (fail)
import           SharingInterface
import qualified Tree

import           Control.Applicative      (Alternative (..))
import           Control.Monad            (MonadPlus (..), liftM2)
import qualified Control.Monad.State.Lazy as MS (State, evalState, get, put)


-- Non-determinism effect--
---------------------------
data ND cnt = Fail' | Choice' (Maybe (Int, Int)) cnt cnt
  deriving (Functor, Show)

pattern Fail <- (project -> Just Fail')
pattern Choice m p q <- (project -> Just (Choice' m p q))

fail :: (ND ⊂ sig) => Prog sig a
fail = inject Fail'

choice :: (ND ⊂ sig) => Prog sig a -> Prog sig a -> Prog sig a
choice p q = inject (Choice' Nothing p q)

choiceID :: (ND ⊂ sig) => Maybe (Int, Int) -> Prog sig a -> Prog sig a -> Prog sig a
choiceID m p q = inject (Choice' m p q)

runND :: (Functor sig) => Prog (ND + sig) a -> Prog sig (Tree.Tree a)
runND (Return a) = return (Tree.Leaf a)
runND Fail       = return Tree.Failed
runND (Choice m p q ) = do
  pt <- runND p
  qt <- runND q
  return (Tree.Choice m pt qt)
runND (Other op) = Op (fmap runND op)

-- Sharing effect --
--------------------
data Share cnt = BShare' Int cnt | EShare' Int cnt
  deriving (Functor, Show)

pattern BShare i p <- (project -> Just (BShare' i p))
pattern EShare i p <- (project -> Just (EShare' i p))

runShare :: (Functor sig, ND ⊂ sig) => Prog (Share + sig) a -> (Prog sig a)
runShare = bshare

bshare :: (ND ⊂ sig) => Prog (Share + sig) a -> Prog sig a
bshare (Return a)   = return a
bshare (BShare i p) = MS.evalState (eshare [i] p) i >>= bshare
bshare (EShare _ p) = error "bshare: mismatched Eshare"
bshare (Other op)   = Op (fmap bshare op)

eshare :: (ND ⊂ sig)
       => [Int] -> Prog (Share + sig) a -> MS.State Int (Prog sig (Prog (Share + sig) a))
eshare  _ (Return a) = return $ return (Return a)
eshare is (BShare i p)  = eshare (i:is) p
eshare [] (EShare _ _) = error "eshare: mismatched EShare"
eshare [i] (EShare j p) | i == j = return $ return p
                        | otherwise = error $ "eshare: wrong scope"
eshare (i:is) (EShare j p)  | i == j = eshare is p
                            | otherwise = error "eshare: crossing scopes"
eshare _ Fail          = return fail
eshare is (Choice Nothing p q) = do
  n <- MS.get
  MS.put (n + 1)
  p' <- eshare is p
  q' <- eshare is q
  return $ choiceID (Just (head is, n)) p' q'
eshare _ (Choice (Just _) _ _) = error "Choice already shared!"
eshare is (Other op) = do
  n <- MS.get
  return $ Op (fmap (\p -> MS.evalState (eshare is p) n) op)

-- interface implementation --
------------------------------
type NDShare = Prog (State Int + Share + ND + Void)

runCurry :: NDShare a -> Tree.Tree a
runCurry = run . runND . runShare . fmap snd . runState 1

instance (Functor sig, ND ⊂ sig) => Alternative (Prog sig) where
  empty = fail
  (<|>) = choice

instance (Functor sig, ND ⊂ sig) => MonadPlus (Prog sig) where
  mplus = choice
  mzero = fail

instance (Share ⊂ sig, State Int ⊂ sig, ND ⊂ sig) => Sharing (Prog sig) where
  share p = do
    i <- get
    put (i + 1)
    return $ do
      inject (BShare' i (return ()))
      x <- p
      k <- get
      put i
      x' <- shareArgs share x
      put (k :: Int)
      inject (EShare' i (return ()))
      return x'

sharen :: (Shareable (Prog sig) a, Share ⊂ sig, State Int ⊂ sig, ND ⊂ sig)
       => Int -> Prog sig a -> Prog sig (Prog sig a)
sharen _ (BShare n p) = inject (BShare' n (sharen n p))
sharen n p = return $ do
  begin
  x <- p
  x' <- shareArgs (sharen n) x
  end
  return x
  where
    begin = inject (BShare' n (return ()))
    end   = inject (EShare' n (return ()))

instance AllValues NDShare where
  allValues = runCurry . nf

type T = Share + ND + Void
deriving instance Show a => Show (Prog (Share + ND + Void) a)
