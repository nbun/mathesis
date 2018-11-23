{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.PrimM where

import Control.Monad (MonadPlus(..))

import SharingInterface

--------------------------------------
-- convience functions for booleans --
--------------------------------------

trueM :: Monad m => m Bool
trueM = return True

falseM :: Monad m => m Bool
falseM = return False

----------------------------------------------
-- random function definitions for booleans --
----------------------------------------------
coin :: MonadPlus m => m Bool
coin = return True `mplus` return False

orM :: Monad m => m Bool -> m Bool -> m Bool
orM mb1 mb2 = mb1 >>= \b1 -> case b1 of
                              True -> return True
                              False -> mb2

notM :: Monad m => m Bool -> m Bool
notM st = fmap not st

-----------------------------------------------
-- Shareable instances for primitive types --
-----------------------------------------------

instance Sharing m => Shareable m () where
    shareArgs _ = return

instance Sharing m => Shareable m Bool where
    shareArgs _ = return

instance Sharing m => Shareable m Int where
    shareArgs _ = return