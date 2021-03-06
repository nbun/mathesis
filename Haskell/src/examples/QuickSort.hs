{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE StandaloneDeriving        #-}

-- Quicksort example
import           Control.Monad         (MonadPlus (..), guard, liftM)
import           Data.Functor.Identity (Identity (..))
import           System.Environment    (getArgs)

import           Pretty
import           SharingInterface

import           Data.ListM
import           Data.PairM
import           Data.PrimM
import           Convert

-- import whatever implementation you like to test
import           CallTimeChoice

testList1, testList2, testList3 :: [Int]
testList1 = [5,42,3,1]
testList2 = [5,42,3,1,1337,51,123,125]
testList3 = [5,42,3,1,1337,51,123,125,347,174,1000]

partitionM :: MonadPlus m
           => (m Int -> m Bool) -> m (List m Int) -> m (Pair m (List m Int))
partitionM mp = foldrM (selectM mp) (pairM nil nil)

selectM :: MonadPlus m
        => (m a -> m Bool) -> m a -> m (Pair m (List m a)) -> m (Pair m (List m a))
selectM mp mx mpa = do
  Pair mxs mys <- mpa
  b <- mp mx
  if b
    then pairM (cons mx mxs) mys
    else pairM mxs (cons mx mys)

quicksortM :: (Sharing m, MonadPlus m)
           => (m Int -> m Int -> m Bool) -> m (List m Int) -> m (List m Int)
quicksortM mp mxs = mxs >>=
  \xs -> case xs of
           Nil -> nil
           Cons my mys ->
             do p <- share (partitionM (mp my) mys)
                appM (appM (quicksortM mp (first p))
                           (cons my nil))
                     (quicksortM mp (second p))

geqM :: (Ord a,MonadPlus m) => m a -> m a -> m Bool
geqM mx my = mx >>= \x -> my >>= \y -> return (x >= y)

-- Tests Quicksort as a permutation generator
testPerm :: [Int] -> IO ()
testPerm xs = do
  let result = quicksortM (\_ _ -> coin) (convert xs :: NDShare (List NDShare Int))
  mapM_ pprint (collectVals result :: [List Identity Int])

-- Tests Quicksort as a sorting function
testSort :: [Int] -> IO ()
testSort xs = do
  let result = quicksortM geqM (convert xs :: NDShare (List NDShare Int))
  mapM_ pprint (collectVals result :: [List Identity Int])
