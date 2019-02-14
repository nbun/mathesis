{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ViewPatterns              #-}

module CallTimeChoiceHO where

import           Control.Applicative    (Alternative (..))
import           Control.Monad.Identity hiding (fail)
import           HO
import           Prelude                hiding (fail, (||))
import           Pretty
import           SharingInterface
import qualified Tree

-- HND
----------
type ID = (Int, Int, Int)

data HND m a = Fail' | Choice' (Maybe ID) (m a) (m a)
  deriving (Show, Functor)

instance HFunctor HND where
  hmap _ Fail'           = Fail'
  hmap t (Choice' m x y) = Choice' m (t x) (t y)


instance Syntax HND where
  emap _ Fail'           = Fail'
  emap f (Choice' m x y) = Choice' m (f x) (f y)

  handle _ _   Fail'     = Fail'
  handle c hdl (Choice' m x y) = let handle z = hdl (fmap (const z) c)
                                 in Choice' m (handle x) (handle y)

pattern Fail <- (project -> Just Fail')

fail :: (HND <: sig) => Prog sig a
fail = inject Fail'

pattern Choice m p q <- (project -> Just (Choice' m p q))

(||) :: (HND <: sig) => Prog sig a -> Prog sig a -> Prog sig a
p || q = inject (Choice' Nothing p  q)

choice :: (HND <: sig) => Maybe ID -> Prog sig a -> Prog sig a -> Prog sig a
choice m p q = inject (Choice' m p q)

runND :: (Syntax sig) => Prog (HND + sig) a -> Prog sig (Tree.Tree a)
runND (Return a) = return (Tree.Leaf a)
runND Fail       = return Tree.Failed
runND (Choice m p q ) = do
  pt <- runND p
  qt <- runND q
  return (Tree.Choice m pt qt)
runND (Other op) = Op (handle (Tree.Leaf ()) hdl op)
  where
    hdl :: (Syntax sig)
        => forall x. Tree.Tree (Prog (HND + sig) x) -> Prog sig (Tree.Tree x)
    hdl Tree.Failed   = return Tree.Failed
    hdl (Tree.Leaf p) = runND p
    hdl (Tree.Choice m p q) = do
      pt <- hdl p
      qt <- hdl q
      return $ Tree.Choice m pt qt

-- HShare
-------
data HShare m a = forall x. Share' (Int, Int) (m x) (x -> m a)

instance Functor m => Functor (HShare m) where
  fmap f (Share' i p k) = Share' i p (fmap f . k)

instance HFunctor HShare where
  hmap t (Share' i p k) = Share' i (t p) (t . k)

instance Syntax HShare where
  emap f (Share' i p k) = Share' i p (f . k)

  handle c hdl (Share' i p k) = Share' i (hdl (fmap (const p) c)) (hdl . fmap k)

pattern Share i p x <- (project -> Just (Share' i p x))

runShare :: (Syntax sig, HND <: sig) => Prog (HShare + sig) a -> Prog sig a
runShare p = fmap runIdentity $ rShare p

shares :: (HShare <: sig) => (Int, Int) -> Prog sig a -> Prog sig a
shares i p = inject (Share' i p return)

rShare :: (Syntax sig, HND <: sig) => Prog (HShare + sig) a
         -> Prog sig (Identity a)
rShare (Return a)  = fmap Identity (return a)
rShare Fail        = fail
rShare (Share i p k) = go i 1 p >>= \r -> rShare (k $ runIdentity r)
  where
    go :: (Syntax sig, HND <: sig)
       => (Int, Int) -> Int -> Prog (HShare + sig) a -> Prog sig (Identity a)
    go _ _ (Return a )    = fmap Identity $ return a
    go _ _ (Fail     )    = fail
    go _ n (Share i p k)    = go i 1 p >>= \r -> rShare (k $ runIdentity r)
    go i@(l,r) n (Choice _ p q) = let n' = n + 1
                                      p' = go i n' p
                                      q' = go i n' q
                                  in choice (Just (l, r, n)) p' q'
    go i n (Other op )    = Op (handle (Identity ()) hdl op)
      where
        hdl :: (Syntax sig, HND <: sig)
            => forall x. Identity (Prog (HShare + sig) x) -> Prog sig (Identity x)
        hdl (Identity p) = go i n p
rShare (Other op)  = Op (handle (Identity ()) hdl op)
  where hdl imx = rShare (runIdentity imx)

-- state effect --
------------------
data HState s m a = Get' (s -> m a)
                  | Put' s (m a)


instance HFunctor (HState m) where
  hmap t (Get' f)   = Get' (t . f)
  hmap t (Put' s p) = Put' s (t p)

instance Syntax (HState m) where
  emap f (Get' g)   = Get' (f . g)
  emap f (Put' s p) = Put' s (f p)

  handle c hdl (Get' f)   = Get' (\s -> hdl (fmap (const (f s)) c))
  handle c hdl (Put' s p) = Put' s (hdl (fmap (const p) c))

pattern Get k <- (project -> Just (Get' k))

get :: (HState s <: sig) => Prog sig s
get = inject (Get' return)

pattern Put s k <- (project -> Just (Put' s k))

put :: (HState s <: sig) => s -> Prog sig ()
put s = inject (Put' s (return ()))

runState :: Syntax sig => s -> Prog (HState s + sig) a -> Prog sig (s, a)
runState s (Return a) = return (s, a)
runState s (Get k)    = runState s (k s)
runState s (Put s' k) = runState s' k
runState s (Other op) = Op (handle (s, ()) (uncurry runState) op)


-- interface implementation --
------------------------------
type NDShare = Prog (HState (Int, Int) + HShare + HND + HVoid)

runCurry :: NDShare a -> Tree.Tree a
runCurry = run . runND . runShare . fmap snd . runState (0,0)

instance (Syntax sig, HND <: sig) => Alternative (Prog sig) where
  empty = fail
  (<|>) = (||)

instance (Syntax sig, HND <: sig) => MonadPlus (Prog sig) where
  mplus = (||)
  mzero = fail

instance (HState (Int, Int) <: sig, HShare <: sig, HND <: sig) => Sharing (Prog sig) where
  share p = do
    (i, j) <- get
    put (i + 1, j)
    let p' = do
          put (i, j + 1)
          x <- p
          x' <- shareArgs share x
          return x'
    return $ shares (i, j) p'

instance AllValues NDShare where
  allValues = runCurry . nf

-- deriving instance Show a => Show (Prog (HShare + HND + HVoid) a)

-- instance (Pretty a, Show a) => Pretty (Prog (HShare + HND + HVoid) a) where
--   pretty' (Return x)     _ = pretty x
--   pretty' (Share i p)   w = "<" ++ si ++ " " ++ pretty' p (w + 2 + 2 * length si) ++ si ++ ">"
--     where si = show i
--   pretty' Fail           _ = "!"
--   pretty' (Choice m p q) wsp =
--     "? " ++  showID m
--     ++ "\n" ++ replicate wsp ' ' ++ "├── " ++ pretty' p (wsp+6)
--     ++ "\n" ++ replicate wsp ' ' ++ "└── " ++ pretty' q (wsp+6)
--     where showID Nothing  = ""
--           showID (Just x) = show x

--   pretty = flip pretty' 0

-- instance (Pretty a, Show a) => Pretty (Prog (HND + HVoid) a) where
--  pretty' (Return x)     _ = pretty x
--  pretty' Fail           _ = "!"
--  pretty' (Choice m p q) wsp =
--    "? " ++  showID m
--    ++ "\n" ++ replicate wsp ' ' ++ "├── " ++ pretty' p (wsp+6)
--    ++ "\n" ++ replicate wsp ' ' ++ "└── " ++ pretty' q (wsp+6)
--    where showID Nothing  = ""
--          showID (Just x) = show x

--  pretty = flip pretty' 0


prettyProgNoShare :: (Pretty a, Show a)
                  => Int -> [Int] -> [Int] -> Prog (HND + HVoid) a -> String
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

instance (Pretty a, Show a) => Pretty (Prog (HND + HVoid) a) where
  pretty' p _ = prettyProgNoShare 0 [] [] p

  pretty = flip pretty' 0



