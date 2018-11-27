module Tree where

type ID = (Int, Int)

data Tree a = Failed
            | Leaf a
            | Choice (Maybe ID) (Tree a) (Tree a)
  deriving Show
