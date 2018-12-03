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
import           Pretty
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
bshare (BShare i p) = eshare 1 [i] p >>= bshare
bshare (EShare _ p) = error "bshare: mismatched Eshare"
bshare (Other op)   = Op (fmap bshare op)

eshare :: (ND ⊂ sig)
       => Int -> [Int] -> Prog (Share + sig) a -> Prog sig (Prog (Share + sig) a)
eshare next scopes prog = --trace (show scopes) $
  case prog of
    Return a   -> return (Return a)
    BShare i p -> eshare next (i:scopes) p
    EShare j p -> case scopes of
                    []     -> error "eshare: mismatched EShare"
                    [i]    -> if i == j
                              then return p
                              else error "eshare: wrong scope"
                    (i:is) -> if i == j
                              then eshare next is p
                              else error "eshare: crossing scopes"
    Fail       -> fail
    Choice _ p q ->
      let p' = eshare (2 * next)     scopes p
          q' = eshare (2 * next + 1) scopes q
      in choiceID (Just (head scopes, next)) p' q'
    Other op -> Op (fmap (eshare next scopes) op)

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

deriving instance Show a => Show (Prog (Share + ND + Void) a)

instance (Pretty a, Show a) => Pretty (Prog (Share + ND + Void) a) where
  pretty' (Return x)     _ = pretty x
  -- pretty' (BShare _ (EShare _ p)) w = pretty' p w
  pretty' (BShare i p)   w = "<" ++ si ++ " " ++ pretty' p (w + 2 + length si)
    where si = show i
  pretty' (EShare i p)   w =  si ++ "> " ++ pretty' p (w + 2 + length si)
    where si = show i
  pretty' Fail           _ = "!"
  pretty' (Choice m p q) wsp =
    "? " ++  showID m
    ++ "\n" ++ replicate wsp ' ' ++ "├── " ++ pretty' p (wsp+6)
    ++ "\n" ++ replicate wsp ' ' ++ "└── " ++ pretty' q (wsp+6)
    where showID Nothing  = ""
          showID (Just x) = show x

  pretty = flip pretty' 0

instance (Pretty a, Show a) => Pretty (Prog (ND + Void) a) where
 pretty' (Return x)     _ = pretty x
 pretty' Fail           _ = "!"
 pretty' (Choice m p q) wsp =
   "? " ++  showID m
   ++ "\n" ++ replicate wsp ' ' ++ "├── " ++ pretty' p (wsp+6)
   ++ "\n" ++ replicate wsp ' ' ++ "└── " ++ pretty' q (wsp+6)
   where showID Nothing  = ""
         showID (Just x) = show x

 pretty = flip pretty' 0

-- Usage:
-- putStrLn $ pretty $ runShare $ fmap snd $ runState 1 (nf (exOr2 :: NDShare Bool) :: NDShare Bool
-- putStrLn $ pretty $ fmap snd $ runState 1 (nf (exOr2 :: NDShare Bool) :: NDShare Bool)
-- putStrLn $ pretty $ fmap snd $ runState 1 (nf (exShareSingleton :: NDShare (Pair NDShare (List NDShare Bool))) :: NDShare (Pair Identity (List Identity Bool)))
