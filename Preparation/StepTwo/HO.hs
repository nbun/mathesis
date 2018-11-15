{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module HO where
import           Control.Monad          (ap, liftM2)
import           Control.Monad.Identity hiding (fail)
import           Prelude                hiding (fail, (||))

data Prog sig a = Return a | Op (sig (Prog sig) a)

instance Syntax sig => Functor (Prog sig) where
  fmap f (Return x) = Return (f x)
  fmap f (Op op)    = Op (emap (fmap f) op)

instance Syntax sig => Applicative (Prog sig) where
  pure = return
  (<*>) = ap

type f --> g = forall x . f x -> g x

class HFunctor h where
  hmap :: (Functor f , Functor g) => (f --> g) -> (h f --> h g)

class HFunctor sig => Syntax sig where
  emap :: (Monad m) => (m a -> m b) -> (sig m a -> sig m b)
  handle :: (Monad m, Monad n, Functor c) =>
    c () -> (forall x . c (m x) -> n (c x)) -> (sig m a -> sig n (c a))

instance Syntax sig => Monad (Prog sig) where
  return v = Return v

  Return v >>= prog = prog v
  Op op    >>= prog = Op (emap (>>= prog) op)

class (Syntax sub, Syntax sup) => sub ⊂ sup where
  inj :: sub m a -> sup m a
  prj :: sup m a -> Maybe (sub m a)

data (sig1 + sig2) (m :: * -> *) a = Inl (sig1 m a) | Inr (sig2 m a)

infixr 0 +

instance {-# OVERLAPPING #-}
  (Syntax sig1, Syntax sig2) => sig1 ⊂ (sig1 + sig2) where
  inj = Inl
  prj (Inl fa) = Just fa
  prj _        = Nothing

instance {-# OVERLAPPABLE #-}
  (Syntax sig1, sig ⊂ sig2) => sig ⊂ (sig1 + sig2) where
  inj = Inr . inj
  prj (Inr ga) = prj ga
  prj _        = Nothing

instance (HFunctor sig1 , HFunctor sig2 ) => HFunctor (sig1 + sig2) where
  hmap t (Inl op) = Inl (hmap t op)
  hmap t (Inr op) = Inr (hmap t op)

instance (Syntax sig1, Syntax sig2 ) => Syntax (sig1 + sig2 ) where
  emap f (Inl op) = Inl (emap f op)
  emap f (Inr op) = Inr (emap f op)

  handle c hdl (Inl op) = Inl (handle c hdl op)
  handle c hdl (Inr op) = Inr (handle c hdl op)

newtype (Lift sig) (m :: * -> *) a = Lift (sig (m a))

instance Functor sig => HFunctor (Lift sig) where
  hmap t (Lift op) = Lift (fmap t op)

instance Functor sig => Syntax (Lift sig) where
  emap f (Lift op) = Lift (fmap f op)
  handle c hdl (Lift op) =
    Lift (fmap (\p -> hdl (fmap (const p) c)) op)

inject :: (sub ⊂ sup) => sub (Prog sup) a -> Prog sup a
inject = Op . inj

project :: (sub ⊂ sup) => Prog sup a -> Maybe (sub (Prog sup) a)
project (Op s) = prj s
project _      = Nothing
