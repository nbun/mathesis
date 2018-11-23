{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE StandaloneDeriving        #-}

-- to compile, run:
-- ghc -O2 --make TestSharing.hs

-- $ time ./permsort 20
-- real 0m14.049s
-- user 0m13.990s

-- time ./permsort.mcc 20
-- real 0m13.121s
-- user 0m10.900s

-- Other implementations using GHC 7.0.3

-- continuation monad with unevaluated thunks in store
-- user 0m37.073s

-- continuation monad with fewer store operations
-- user 0m29.517s

-- SharingRef (GHC 8.0.2)
-- user 0m29.114s

import           Control.Monad         (MonadPlus (..), guard, liftM)
import           Data.Functor.Identity (Identity (..))
import           System.Environment    (getArgs)

import           Pretty
import           SharingInterface

import           Data.ListM
import           Data.PrimM

-- import whatever implementation you like to test
import           ScopeShareState

class Convertible m a b where
    convert :: a -> m b

instance (Monad m) => Convertible m Int Int where
    convert = return

instance (Monad m) => Convertible m Bool Bool where
    convert = return

instance (Monad m) => Convertible m [Int] [Int] where
    convert = return

instance (Monad m, Convertible m a b) => Convertible m (List m a) [b] where
    convert Nil = return []
    convert (Cons mx mxs) = (mx >>= convert) >>= \y ->
                            (mxs >>= convert) >>= \ys ->
                            return (y:ys)

instance (Monad m, Convertible m a b) => Convertible m [a] (List m b) where
    convert []     = nil
    convert (x:xs) = cons (convert x) (convert xs)

deriving instance Show a => Show (List NDShare a)
deriving instance Show a => Show (List Identity a)

main :: IO ()
main = do
  n <- liftM (read.head) getArgs
  testSort [1..n]

testList1, testList2, testList3 :: [Int]
testList1 = [5,42,3,1]
testList2 = [5,42,3,1,1337,51,123,125]
testList3 = [5,42,3,1,1337,51,123,125,347,174,1000]

testSort :: [Int] -> IO ()
testSort xs = do
  let result = sort (convert xs :: NDShare (List NDShare Int))
  mapM_ pprint (collectVals result :: [List Identity Int])

testSortHead :: [Int] -> IO ()
testSortHead xs = do
  let result = headM (sort (convert xs :: NDShare (List NDShare Int)))
  mapM_ pprint (collectVals result :: [Int])

perm :: (Sharing m, MonadPlus m) => m (List m Int) -> m (List m Int)
perm mxs = mxs >>= \xs -> case xs of
                              Nil         -> nil
                              Cons mx mxs -> insert mx (perm mxs)

insert :: (Sharing m, MonadPlus m) => m Int -> m (List m Int) -> m (List m Int)
insert e l = share e >>= \e' ->
     cons e' l
     `mplus` do
        ys <- l
        case ys of
          Cons x xs -> cons x (insert e' xs)
          _         -> mzero

member :: MonadPlus m => m (List m Int) -> m Int
member mxs = mxs >>= \xs -> case xs of
                              Nil         -> mzero
                              Cons my mys -> my `mplus` member mys
-- insert :: MonadPlus m => m a -> m (List m a) -> m (List m a)
-- insert e l = cons e l
--      `mplus` do
--         ys <- l
--         case ys of
--           Cons x xs -> cons x (insert e xs)
--           _         -> mzero

shareList :: (Normalform m a a, Shareable m a, MonadPlus m, Sharing m) =>
             m (List m a) -> m (m (List m a))
shareList sxs = do
  xs <- sxs
  case xs of
       Nil -> return nil
       Cons sy sys -> do y <- share sy
                         ys <- shareList sys
                         return (cons y ys)

sort :: (MonadPlus m, Sharing m) => m (List m Int) -> m (List m Int)
sort l = do
  xs <- share (perm l)
  b <- isSorted xs
  case b of
    True  -> xs
    False -> mzero

isSorted :: Monad m => m (List m Int) -> m Bool
isSorted mxs = mxs >>= \xs -> case xs of
                                   Nil         -> return True
                                   Cons my mys -> isSorted' my mys

isSorted' :: Monad m => m Int -> m (List m Int) -> m Bool
isSorted' mx mxs = mxs >>= \xs -> case xs of
                                       Nil -> return True
                                       Cons my mys -> do
                                         x <- mx
                                         y <- my
                                         if x <= y
                                           then isSorted' (return y) mys
                                           else return False
