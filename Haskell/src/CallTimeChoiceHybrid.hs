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

module CallTimeChoiceHybrid where
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


-- Non-determinism effect --
---------------------------- 
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
data Share cnt = Share' Int cnt
  deriving (Functor, Show)

pattern Share i p <- (project -> Just (Share' i p))

runShare :: (Functor sig, ND ⊂ sig) => Prog (Share + sig) a -> (Prog sig a)
runShare = bshare

bshare :: (ND ⊂ sig) => Prog (Share + sig) a -> Prog sig a
bshare (Return a)   = return a
bshare (Share i p) = eshare 1 i p >>= bshare
bshare (Other op)   = Op (fmap bshare op)

eshare :: (ND ⊂ sig)
       => Int -> Int -> Prog (Share + sig) a -> Prog sig (Prog (Share + sig) a)
eshare next scope prog =
  case prog of
    Return a   -> return (Return a)
    Share i p -> eshare 1 i p
    Fail       -> fail
    Choice Nothing p q ->
      let p' = eshare (2 * next)     scope p
          q' = eshare (2 * next + 1) scope q
      in choiceID (Just (scope, next)) p' q'
    Other op -> Op (fmap (eshare next scope) op)

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
    let p' = do
          x <- p
          put (i + 1)
          x' <- shareArgs share x
          return x'
    return $ inject (Share' i p')

instance AllValues NDShare where
  allValues = runCurry . nf

deriving instance Show a => Show (Prog (Share + ND + Void) a)

instance (Pretty a, Show a) => Pretty (Prog (Share + ND + Void) a) where
  pretty' (Return x)     _ = pretty x
  pretty' (Share i p)   w =
    "<" ++ si ++ " "
    ++ pretty' p (w + 2 + 2 * length si)
    ++ si ++ ">"
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
