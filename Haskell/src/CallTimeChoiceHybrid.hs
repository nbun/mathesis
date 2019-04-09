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

---------------------------------------------------------
-- Hybrid implementation                               --
-- DOES NOT WORK; ONLY KEPT FOR DOCUMENTATION PURPOSES --
---------------------------------------------------------

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

----------------------------
-- Non-determinism effect --
----------------------------

type ID = (Int, Int, Int)

data ND cnt = Fail' | Choice' (Maybe ID) cnt cnt
  deriving (Functor, Show)

pattern Fail <- (project -> Just Fail')
pattern Choice m p q <- (project -> Just (Choice' m p q))

fail :: (ND :<: sig) => Prog sig a
fail = inject Fail'

choice p q = inject (Choice' Nothing p q)

choiceID :: (ND :<: sig) => Maybe ID -> Prog sig a -> Prog sig a -> Prog sig a
choiceID m p q = inject (Choice' m p q)

runND :: (Functor sig) => Prog (ND :+: sig) a -> Prog sig (Tree.Tree a)
runND (Return a) = return (Tree.Leaf a)
runND Fail       = return Tree.Failed
runND (Choice m p q ) = do
  pt <- runND p
  qt <- runND q
  return (Tree.Choice m pt qt)
runND (Other op) = Op (fmap runND op)

--------------------
-- Sharing effect --
--------------------

data Share cnt = Share' (Int, Int) cnt
  deriving (Functor, Show)

pattern Share i p <- (project -> Just (Share' i p))

share' :: (Share :<: sig) => (Int, Int) -> Prog sig a -> Prog sig a
share' i p = inject (Share' i p)

runShare :: (Functor sig, ND :<: sig) => Prog (Share :+: sig) a -> (Prog sig a)
runShare (Return a)  = return a
runShare (Share i p) = nameChoices i 1 p
  where
    nameChoices :: (ND :<: sig) => (Int, Int) -> Int -> Prog (Share :+: sig) a -> Prog sig a
    nameChoices scope@(l,r) next prog = case prog of
      Return a  -> Return a
      Share i p -> nameChoices i 1 p
      Fail      -> fail
      Choice _ p q ->
        let next' = next + 1
            p' = nameChoices scope next' p
            q' = nameChoices scope next' q
        in choiceID (Just (l, r, next)) p' q'
      Other op -> Op (fmap (nameChoices scope next) op)
runShare (Other op)  = Op (fmap runShare op)

------------------------------
-- interface implementation --
------------------------------

type NDShare = Prog (State (Int, Int) :+: Share :+: ND :+: Void)

runCurry :: NDShare a -> Tree.Tree a
runCurry = run . runND . runShare . fmap snd . runState (0, 0)

instance (Functor sig, ND :<: sig) => Alternative (Prog sig) where
  empty = fail
  (<|>) = choice

instance (Functor sig, ND :<: sig) => MonadPlus (Prog sig) where
  mplus = choice
  mzero = fail

instance (Share :<: sig, State (Int, Int) :<: sig, ND :<: sig) => Sharing (Prog sig) where
  share p = do
    (i,j) <- get
    put (i + 1, j)
    return . share' (i, j) $ do
      put (i, j + 1)
      x <- p
      x' <- shareArgs share x
      put (i + 1, j)
      return x'

instance AllValues NDShare where
  allValues = runCurry . nf

------------------------------
-- Pretty printing programs --
------------------------------

deriving instance Show a => Show (Prog (Share :+: ND :+: Void) a)

instance (Pretty a, Show a) => Pretty (Prog (Share :+: ND :+: Void) a) where
  pretty' p _ = prettyProg 0 [] [] p
  pretty = flip pretty' 0

instance (Pretty a, Show a) => Pretty (Prog (ND :+: Void) a) where
  pretty' p _ = prettyProgNoShare 0 [] [] p
  pretty = flip pretty' 0

prettyProg :: (Pretty a, Show a)
           => Int -> [Int] -> [(Int, Int)] -> Prog (Share :+: ND :+: Void) a -> String
prettyProg _ _ scps (Return x)  = pretty x ++ concatMap (\scp -> ' ' : show scp ++ ">") scps
prettyProg wsp ls scps (Share i p) =
  "<" ++ si ++ " " ++ prettyProg (wsp + l) ls (i:scps) p
  where si = show i
        l  = length si + 2
prettyProg _ _ _ Fail         = "!"
prettyProg wsp ls scps (Choice m p q) =
  "? " ++  showID m
  ++ "\n" ++ lines ++ "├── " ++ prettyProg (wsp + 4) (wsp:ls) scps p
  ++ "\n" ++ lines ++ "└── " ++ prettyProg (wsp + 4) ls       scps q
  where lines = printLines (wsp:ls)

prettyProgNoShare :: (Pretty a, Show a)
                  => Int -> [Int] -> [Int] -> Prog (ND :+: Void) a -> String
prettyProgNoShare _ _    scps (Return x)     =
  pretty x ++ concatMap (\scp -> ' ' : show scp ++ ">") scps
prettyProgNoShare _ _    _    Fail           = "!"
prettyProgNoShare wsp ls scps (Choice m p q) =
  "? " ++  showID m
  ++ "\n" ++ lines ++ "├── " ++ prettyProgNoShare (wsp + 4) (wsp:ls) scps p
  ++ "\n" ++ lines ++ "└── " ++ prettyProgNoShare (wsp + 4) ls       scps q
  where lines = printLines (wsp:ls)
