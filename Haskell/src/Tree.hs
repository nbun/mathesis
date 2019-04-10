{-# LANGUAGE DeriveFunctor #-}
-- Definition of choice trees and the depth-first search algorithm
module Tree where

import qualified Data.Map as Map

-- The first two Ints of an ID are the sharing scope ID, the third
-- component is a counter assigned by the handler
type ID = (Int, Int, Int)

data Tree a = Failed
            | Leaf a
            | Choice (Maybe ID) (Tree a) (Tree a)
  deriving (Show, Functor)

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
      Just L  -> dfs mem t1
      Just R  -> dfs mem t2

dfsWithEmpty :: Tree a -> [a]
dfsWithEmpty = dfs Map.empty
