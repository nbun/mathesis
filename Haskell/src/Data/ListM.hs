{-# LANGUAGE StandaloneDeriving, FlexibleInstances, MultiParamTypeClasses #-}

module Data.ListM where

import Data.PairM

import Data.Functor.Identity (Identity(..))
import Control.Monad (MonadPlus(..))

import SharingInterface
import Pretty

----------------------------------------------------
-- data type definition and convenience functions --
----------------------------------------------------
data List m a = Nil | Cons (m a) (m (List m a))

cons :: Monad m => n a -> n (List n a) -> m (List n a)
cons x xs = return (Cons x xs)

nil :: Monad m => m (List n a)
nil = return Nil

--------------------------
-- type class instances --
--------------------------
deriving instance Eq a => Eq (List Identity a)

instance Pretty a => Pretty (List Identity a) where
   pretty xs = "[" ++ prettyList xs ++ "]"
    where
     prettyList Nil = ""
     prettyList (Cons sx (Identity Nil)) = pretty (runIdentity sx)
     prettyList (Cons sx sxs) = pretty (runIdentity sx) ++ "," ++ prettyList (runIdentity sxs)

instance (Normalform n a b, Monad m, Monad n) =>
    Normalform n (List n a) (List m b) where
    nf stxs = stxs >>= \xs ->
                case xs of
                    Nil -> nil
                    Cons sx sxs -> nf sx >>= \x ->
                                   nf sxs >>= \xs ->
                                   cons (return x) (return xs)

instance (Sharing m, Shareable m a) => Shareable m (List m a) where
    shareArgs f Nil = nil
    shareArgs f (Cons sy sys) = do sy' <- f sy
                                   sys' <- f sys
                                   cons sy' sys'

-------------------------------------------
-- random function definitions for lists --
-------------------------------------------
dupl :: Monad m => m a -> m (List m a)
dupl sx = cons sx (cons sx nil)

duplShare :: (Monad m, Sharing m, Shareable m a) => m a -> m (List m a)
duplShare sx = share sx >>= \sx' -> cons sx' (cons sx' nil)

headM :: MonadPlus m => m (List m a) -> m a
headM sxs = sxs >>= \ xs -> case xs of
                            Nil -> mzero
                            Cons sx _ -> sx

heads :: MonadPlus m => m (List m a) -> m (Pair m a)
heads sxs = pairM (headM sxs) (headM sxs)

appM :: MonadPlus m => m (List m a) -> m (List m a) -> m (List m a)
appM fxs fys = fxs >>= \xs -> case xs of
                                Nil -> fys
                                Cons fz fzs -> cons fz (appM fzs fys)

lengthM :: MonadPlus m => m (List m a) -> m Int
lengthM fxs = fxs >>= \xs -> case xs of
                               Nil -> return 0
                               Cons _ fys -> lengthM fys >>= \j -> return (1 + j)

foldrM :: MonadPlus m => (m a -> m b -> m b) -> m b -> m (List m a) -> m b
foldrM f fe fxs = fxs >>= \xs -> case xs of
                                   Nil -> fe
                                   Cons fy fys -> f fy (foldrM f fe fys)