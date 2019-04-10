{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- Converts data types into the corresponding lifted version
module Convert where

import           Data.ListM
import           Data.PairM
import           Data.PrimM

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

