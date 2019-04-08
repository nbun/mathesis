{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- Definition of lifted functions for primitive values
module Data.PrimM where

import Control.Monad (MonadPlus(..))

import SharingInterface

--------------------------------------
-- convenience functions for booleans --
--------------------------------------

trueM :: Monad m => m Bool
trueM = return True

falseM :: Monad m => m Bool
falseM = return False

---------------------------------------
-- function definitions for booleans --
---------------------------------------
coin :: MonadPlus m => m Bool
coin = return True `mplus` return False

orM :: Monad m => m Bool -> m Bool -> m Bool
orM mb1 mb2 = mb1 >>= \b1 -> case b1 of
                              True -> return True
                              False -> mb2

notM :: Monad m => m Bool -> m Bool
notM st = fmap not st

----------------------------------------
-- convenience functions for integers --
----------------------------------------

intM :: Monad m => Int -> m Int
intM n = return n

---------------------------------------
-- function definitions for integers --
---------------------------------------
coini :: MonadPlus m => m Int
coini = return 0 `mplus` return 1

addM :: Monad m => m Int -> m Int -> m Int
addM mi1 mi2 = do
  i1 <- mi1
  i2 <- mi2
  return $ i1 + i2

duplicate :: Monad m => m a -> m (a, a)
duplicate a = do u <- a
                 v <- a
                 return (u,v)

-----------------------------------------------
-- Shareable instances for primitive types --
-----------------------------------------------

instance Sharing m => Shareable m () where
    shareArgs _ = return

instance Sharing m => Shareable m Bool where
    shareArgs _ = return

instance Sharing m => Shareable m Int where
    shareArgs _ = return
