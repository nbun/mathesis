{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}

-- Definition of lifted pairs
module Data.PairM where

import           Data.Functor.Identity (Identity (..))
import           Pretty
import           SharingInterface

----------------------------------------------------
-- data type definition and convenience functions --
----------------------------------------------------
data Pair m a = Pair (m a) (m a)

pairM :: Monad m => n a -> n a -> m (Pair n a)
pairM x1 x2 = return (Pair x1 x2)

--------------------------
-- type class instances --
--------------------------
deriving instance Eq a => Eq (Pair Identity a)

instance Pretty a => Pretty (Pair Identity a) where
   pretty (Pair sx sy) = "(" ++ pretty sx ++ "," ++ pretty sy ++ ")"

instance (Normalform n a b, Monad m, Monad n) =>
    Normalform n (Pair n a) (Pair m b) where
    nf stp = stp >>= \(Pair sp1 sp2) ->
             nf sp1 >>= \b1 ->
             nf sp2 >>= \b2 ->
             pairM (return b1) (return b2)

instance (Sharing m, Shareable m a) => Shareable m (Pair m a) where
    shareArgs f (Pair sx sy) = do sx' <- f sx
                                  sy' <- f sy
                                  pairM sx' sy'

------------------------------------
-- function definitions for pairs --
------------------------------------
first :: Monad m => m (Pair m a) -> m a
first st = st >>= \ (Pair x _) -> x

second :: Monad m => m (Pair m a) -> m a
second st = st >>= \ (Pair _ x) -> x

dup' :: Monad m => m (Pair m Bool) -> m (Pair m Bool)
dup' st = pairM (first st) (first st)

dup :: Monad m => m a -> m (Pair m a)
dup st = pairM st st

dupShare :: (Monad m, Sharing m, Shareable m a) => m a -> m (Pair m a)
dupShare st = share st >>= \st' -> pairM st' st'
