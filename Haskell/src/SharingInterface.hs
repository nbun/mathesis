{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module SharingInterface where

import Control.Monad.Trans.State ( State(..), state, get, put )
import Control.Monad (MonadPlus(..))

import qualified Data.Map as Map

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

----------------------
-- Search algorithm --
----------------------
data Decision = L | R
type Memo = Map.Map ID Decision

dfs :: Memo -> Tree a -> [a]
dfs mem Failed = []
dfs mem (Leaf x) = [x]
dfs mem (Choice Nothing t1 t2) = dfs mem t1 ++ dfs mem t2
dfs mem (Choice (Just n) t1 t2) =
    case Map.lookup n mem of
      Nothing -> dfs (Map.insert n L mem) t1 ++ dfs (Map.insert n R mem) t2
      Just L -> dfs mem t1
      Just R -> dfs mem t2


dfsWithEmpty :: Tree a -> [a]
dfsWithEmpty = dfs Map.empty

--------------------------------------------------------
-- function to collect all values with respect to dfs --
--------------------------------------------------------

collectVals :: (AllValues m, Normalform m a b) => m a -> [b]
collectVals expr = dfsWithEmpty (allValues expr)
