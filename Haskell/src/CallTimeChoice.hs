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


-- Non-determinism effect --
----------------------------
type ID = (Int, Int, Int)

data ND cnt = Fail' | Choice' (Maybe ID) cnt cnt
  deriving (Functor, Show)

pattern Fail <- (project -> Just Fail')
pattern Choice m p q <- (project -> Just (Choice' m p q))

fail :: (ND <: sig) => Prog sig a
fail = inject Fail'

choice :: (ND <: sig) => Prog sig a -> Prog sig a -> Prog sig a
choice p q = inject (Choice' Nothing p q)

choiceID :: (ND <: sig) => Maybe ID -> Prog sig a -> Prog sig a -> Prog sig a
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
data Share cnt = BShare' (Int, Int) cnt | EShare' (Int, Int) cnt
  deriving (Functor, Show)

pattern BShare i p <- (project -> Just (BShare' i p))
pattern EShare i p <- (project -> Just (EShare' i p))

runShare :: (Functor sig, ND <: sig) => Prog (Share + sig) a -> (Prog sig a)
runShare = bshare

bshare :: (ND <: sig) => Prog (Share + sig) a -> Prog sig a
bshare (Return a)   = return a
bshare (BShare i p) = eshare 1 [i] p >>= bshare
bshare (EShare _ p) = error "bshare: mismatched Eshare"
bshare (Other op)   = Op (fmap bshare op)

eshare :: (ND <: sig)
       => Int -> [(Int, Int)] -> Prog (Share + sig) a -> Prog sig (Prog (Share + sig) a)
eshare next scopes prog = --trace (show scopes) $
  case prog of
    Return a   -> return (Return a)
    BShare i p -> eshare 1 (i:scopes) p
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
      let next' = next + 1
          p' = eshare next' scopes p
          q' = eshare next' scopes q
          (l,r) = head scopes
      in choiceID (Just (l, r, next)) p' q'
    Other op -> Op (fmap (eshare next scopes) op)

-- interface implementation --
------------------------------
type NDShare = Prog (State (Int, Int) + Share + ND + Void)

runCurry :: NDShare a -> Tree.Tree a
runCurry = run . runND . runShare . fmap snd . runState (0,0)

instance (Functor sig, ND <: sig) => Alternative (Prog sig) where
  empty = fail
  (<|>) = choice

instance (Functor sig, ND <: sig) => MonadPlus (Prog sig) where
  mplus = choice
  mzero = fail

instance (Share <: sig, State (Int, Int) <: sig, ND <: sig) => Sharing (Prog sig) where
  share p = do
    (i, j) <- get
    put (i + 1, j)
    return $ do
      inject (BShare' (i,j) (return ()))
      put (i, j + 1)
      x <- p
      x' <- shareArgs share x
      inject (EShare' (i,j) (return ()))
      return x'

instance AllValues NDShare where
  allValues = runCurry . nf

deriving instance Show a => Show (Prog (Share + ND + Void) a)

instance (Pretty a, Show a) => Pretty (Prog (Share + ND + Void) a) where
  pretty' p _ = prettyProg 0 [] p

  pretty = flip pretty' 0

prettyProg :: (Pretty a, Show a)
           => Int -> [Int] -> Prog (Share + ND + Void) a -> String
prettyProg _ _ (Return x)  = pretty x
prettyProg wsp ls (BShare i p) =
  "<" ++ si ++ " " ++ prettyProg (wsp + l) ls p
  where si = show i
        l  = length si + 2
prettyProg wsp ls (EShare i p) =
  si ++ "> " ++ prettyProg (wsp + l) ls p
  where si = show i
        l  = length si + 2

prettyProg _ _ Fail         = "!"
prettyProg wsp ls (Choice m p q) =
  "? " ++  showID m
  ++ "\n" ++ lines ++ "├── " ++ prettyProg (wsp + 4) (wsp:ls) p
  ++ "\n" ++ lines ++ "└── " ++ prettyProg (wsp + 4) ls       q
  where showID Nothing  = ""
        showID (Just x) = show x
        lines = printLines (wsp:ls)

prettyProgNoShare :: (Pretty a, Show a)
                  => Int -> [Int] -> [Int] -> Prog (ND + Void) a -> String
prettyProgNoShare _ _    scps (Return x)  = pretty x ++ concatMap (\scp -> ' ' : show scp ++ ">") scps
prettyProgNoShare _ _    _    Fail        = "!"
prettyProgNoShare wsp ls scps (Choice m p q) =
  "? " ++  showID m
  ++ "\n" ++ lines ++ "├── " ++ prettyProgNoShare (wsp + 4) (wsp:ls) scps p
  ++ "\n" ++ lines ++ "└── " ++ prettyProgNoShare (wsp + 4) ls       scps q
  where showID Nothing  = ""
        showID (Just x) = show x
        lines = printLines (wsp:ls)

printLines :: [Int] -> String
printLines = printLines' 0 . reverse
  where
    printLines' p  [x] = replicate (x - p) ' '
    printLines' p (x:xs)  | p == x    = '│' : printLines' (p + 1) xs
                          | otherwise = ' ' : printLines' (p + 1) (x:xs)

instance (Pretty a, Show a) => Pretty (Prog (ND + Void) a) where
  pretty' p _ = prettyProgNoShare 0 [] [] p

  pretty = flip pretty' 0
-- Usage:
-- putStrLn $ pretty $ runShare $ fmap snd $ runState 1 (nf (exOr2 :: NDShare Bool) :: NDShare Bool
-- putStrLn $ pretty $ fmap snd $ runState 1 (nf (exOr2 :: NDShare Bool) :: NDShare Bool)
-- putStrLn $ pretty $ fmap snd $ runState 1 (nf (exShareSingleton :: NDShare (Pair NDShare (List NDShare Bool))) :: NDShare (Pair Identity (List Identity Bool)))
