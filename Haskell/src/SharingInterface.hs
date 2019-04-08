{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

-- Interface for defining explicit sharing implementations
module SharingInterface where

import Control.Monad.Trans.State (State(..), state, get, put )
import Control.Monad (MonadPlus(..))
import Tree

----------------------------
-- type class for sharing --
----------------------------

class MonadPlus s => Sharing (s :: * -> *) where
    share :: Shareable s a => s a -> s (s a)

class AllValues (s :: * -> *) where
    allValues :: (Normalform s a b) => s a -> Tree b

class Shareable m a where
  shareArgs :: Monad n => (forall b. Shareable m b => m b -> n (m b)) -> a -> n a

---------------------------
-- Normalform evaluation --
---------------------------

class Normalform m a b where
    nf :: m a -> m b

----------------------------------------------
-- type class instances for primitive types --
----------------------------------------------

instance Monad m => Normalform m () () where
    nf = id

instance Monad m => Normalform m Int Int where
    nf = id

instance Monad m => Normalform m Bool Bool where
    nf = id


instance Monad m => Normalform m (a,b) (a,b) where
    nf = id

--------------------------------------------------------
-- function to collect all values with respect to dfs --
--------------------------------------------------------

collectVals :: (AllValues m, Normalform m a b) => m a -> [b]
collectVals expr = dfsWithEmpty (allValues expr)
