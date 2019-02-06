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

deriving instance Show a => Show (Prog (One :+: One) a)

nothing :: Prog (One :+: One) a
nothing = inject One
