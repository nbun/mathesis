{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

data Prog sig a = Return a | Op (sig (Prog sig a))
  deriving Functor


instance (Functor sig, Applicative (Prog sig)) => Monad (Prog sig) where
  return v = Return v
  Return v >>= prog = prog v
  Op op >>= prog = Op (fmap (>>= prog) op)

data (sig1 :+: sig2) a = Inl (sig1 a) | Inr (sig2 a)
  deriving (Functor, Show)

data ND p = Fail | Choice p p
  deriving (Show, Functor)

data One p = One
  deriving (Show, Functor)

type NDOne = ND :+: One

prog1 :: Prog (ND :+: One) Int
prog1 = Op (Inl (Choice (Op (Inr One)) (Return 42)))

class (Functor sub, Functor sup) => sub :<: sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance Functor sig => sig :<: sig where
  inj = id
  prj = Just

instance {-# OVERLAPPING #-}
  (Functor sig1, Functor sig2) => sig1 :<: (sig1 :+: sig2) where
  inj = Inl
  prj (Inl fa) = Just fa
  prj _        = Nothing

instance {-# OVERLAPPABLE #-}
  (Functor sig1, sig :<: sig2) => sig :<: (sig1 :+: sig2) where
  inj = Inr . inj
  prj (Inr ga) = prj ga
  prj _        = Nothing

inject :: sig1 :<: sig2 => sig1 (Prog sig2 a) -> Prog sig2 a
inject = Op . inj

deriving instance Show a => Show (Prog (ND :+: One) a)

nothing :: Prog (ND :+: One) a
nothing = inject One

progNDOne' :: Prog (ND :+: One) Int
progNDOne' = inject (Choice (inject One) (Return 42))

project :: (sub :<: sup) => Prog sup a -> Maybe (sub (Prog sup a))
project (Op s) = prj s
project _      = Nothing

evalND :: Prog (ND :+: One) a -> [a]
evalND (Return x) = [x]
evalND p = case project p of
               Just (Choice p1 p2) -> evalND p1 ++ evalND p2
               Just Fail           -> []
               Nothing             -> case project p of
                                        Just One -> []
                                        Nothing  -> []

evalNDOne' :: Prog (ND :+: One) a -> [a]
evalNDOne' (Return x) = [x]
evalNDOne' (project -> Just (Choice p1 p2)) = evalNDOne' p1 ++ evalNDOne' p2
evalNDOne' (project -> Just Fail          ) = []
evalNDOne' (project -> Just One           ) = []

pattern PChoice p q <- (project -> Just (Choice p q))
pattern PFail       <- (project -> Just Fail)
pattern POne        <- (project -> Just One)

evalNDOne'' :: Prog (ND :+: One) a -> [a]
evalNDOne'' (Return    x) = [x]
evalNDOne'' (PChoice p q) = evalNDOne'' p ++ evalNDOne'' q
evalNDOne'' (PFail      ) = []
evalNDOne'' (POne       ) = []


tree :: (ND <: sig) => Int -> Prog sig Int
tree 0 = return 0
tree x = do
  i <- tree (x - 1)
  choice (return $ i + 1) (return $ i - 1)

treeGlobal :: (Int, Tree.Tree Int)
treeGlobal = run . runState 0 . runND . results $ tree 2

treeLocal :: Tree.Tree (Int, Int)
treeLocal = run . runND . runState 0 . results $ tree 2

results :: (ND <: sig, State Int <: sig) => Prog sig a -> Prog sig a
results (Return x) = incr >> return x
  where incr = get >>= put . (+ (1 :: Int))
results Fail       = fail
results (Choice m p q ) = do
  let p' = results p
  let q' = results q
    in choiceID m p' q'
results (Op op) = Op (fmap results op)

