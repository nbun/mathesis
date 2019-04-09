{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Thesis where
import Base

data Choice p = Choice p p
data Fail   p = Fail

progCF :: Prog (Choice :+: Fail) Int
progCF = Op (Inl (Choice (Op (Inr Fail)) (Return 42)))

-- tree :: (ND <: sig) => Int -> Prog sig Int
-- tree 0 = return 0
-- tree x = do
--   i <- tree (x - 1)
--   choice (return $ i + 1) (return $ i - 1)

-- treeGlobal :: (Int, Tree.Tree Int)
-- treeGlobal = run . runState 0 . runND . results $ tree 2

-- treeLocal :: Tree.Tree (Int, Int)
-- treeLocal = run . runND . runState 0 . results $ tree 2

-- results :: (ND <: sig, State Int <: sig) => Prog sig a -> Prog sig a
-- results (Return x) = incr >> return x
--   where incr = get >>= put . (+ (1 :: Int))
-- results Fail       = fail
-- results (Choice m p q ) = do
--   let p' = results p
--   let q' = results q
--     in choiceID m p' q'
-- results (Op op) = Op (fmap results op)

