{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

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
data HND m a = Fail' | Choice' (Maybe (Int, Int)) (m a) (m a)
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

fail :: (HND ⊂ sig) => Prog sig a
fail = inject Fail'

pattern Choice m p q <- (project -> Just (Choice' m p q))

(||) :: (HND ⊂ sig) => Prog sig a -> Prog sig a -> Prog sig a
p || q = inject (Choice' Nothing p  q)

choice :: (HND ⊂ sig) => Maybe (Int, Int) -> Prog sig a -> Prog sig a -> Prog sig a
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
data HShare m a = Share' Int (m a)
  deriving (Show, Functor)

instance HFunctor HShare where
  hmap t (Share' i p) = Share' i (t p)

instance Syntax HShare where
  emap f (Share' i p) = Share' i (f p)

  handle c hdl (Share' i p) = Share' i (hdl (fmap (const p) c))

pattern Share i p <- (project -> Just (Share' i p))

runShare :: (Syntax sig, HND ⊂ sig) => Prog (HShare + sig) a -> Prog sig a
runShare p = fmap runIdentity $ rShare p

shares :: (HShare ⊂ sig) => Int -> Prog sig a -> Prog sig a
shares i p = inject (Share' i p)

rShare :: (Syntax sig, HND ⊂ sig) => Prog (HShare + sig) a
         -> Prog sig (Identity a)
rShare (Return a)  = fmap Identity (return a)
rShare Fail        = fail
rShare (Share i p) = go i 1 p
  where
    go :: (Syntax sig, HND ⊂ sig)
       => Int -> Int -> Prog (HShare + sig) a -> Prog sig (Identity a)
    go _ _ (Return a )    = fmap Identity $ return a
    go _ _ (Fail     )    = fail
    go _ n (Share i p)    = go i 1 p
    go i n (Choice _ p q) = let p' = go i (2 * n) p
                                q' = go i (2 * n + 1) q
                            in choice (Just (i, n)) p' q'
    go i n (Other op )    = Op (handle (Identity ()) hdl op)
      where
        hdl :: (Syntax sig, HND ⊂ sig)
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

get :: (HState s ⊂ sig) => Prog sig s
get = inject (Get' return)

pattern Put s k <- (project -> Just (Put' s k))

put :: (HState s ⊂ sig) => s -> Prog sig ()
put s = inject (Put' s (return ()))

runState :: Syntax sig => s -> Prog (HState s + sig) a -> Prog sig (s, a)
runState s (Return a) = return (s, a)
runState s (Get k)    = runState s (k s)
runState s (Put s' k) = runState s' k
runState s (Other op) = Op (handle (s, ()) (uncurry runState) op)


-- interface implementation --
------------------------------
type NDShare = Prog (HState Int + HShare + HND + HVoid)

runCurry :: NDShare a -> Tree.Tree a
runCurry = run . runND . runShare . fmap snd . runState 1

instance (Syntax sig, HND ⊂ sig) => Alternative (Prog sig) where
  empty = fail
  (<|>) = (||)

instance (Syntax sig, HND ⊂ sig) => MonadPlus (Prog sig) where
  mplus = (||)
  mzero = fail

instance (HState Int ⊂ sig, HShare ⊂ sig, HND ⊂ sig) => Sharing (Prog sig) where
  share p = do
    i <- get
    put (i + 1)
    let p' = do
          x <- p
          put (i + 1)
          x' <- shareArgs share x
          return x'
    return $ shares i p'

instance AllValues NDShare where
  allValues = runCurry . nf

deriving instance Show a => Show (Prog (HShare + HND + HVoid) a)

instance (Pretty a, Show a) => Pretty (Prog (HShare + HND + HVoid) a) where
  pretty' (Return x)     _ = pretty x
  pretty' (Share i p)   w = "<" ++ si ++ " " ++ pretty' p (w + 2 + 2 * length si) ++ si ++ ">"
    where si = show i
  pretty' Fail           _ = "!"
  pretty' (Choice m p q) wsp =
    "? " ++  showID m
    ++ "\n" ++ replicate wsp ' ' ++ "├── " ++ pretty' p (wsp+6)
    ++ "\n" ++ replicate wsp ' ' ++ "└── " ++ pretty' q (wsp+6)
    where showID Nothing  = ""
          showID (Just x) = show x

  pretty = flip pretty' 0

instance (Pretty a, Show a) => Pretty (Prog (HND + HVoid) a) where
 pretty' (Return x)     _ = pretty x
 pretty' Fail           _ = "!"
 pretty' (Choice m p q) wsp =
   "? " ++  showID m
   ++ "\n" ++ replicate wsp ' ' ++ "├── " ++ pretty' p (wsp+6)
   ++ "\n" ++ replicate wsp ' ' ++ "└── " ++ pretty' q (wsp+6)
   where showID Nothing  = ""
         showID (Just x) = show x

 pretty = flip pretty' 0

