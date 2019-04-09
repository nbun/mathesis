{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

-- Definition of the basic effect handler infrastructure
module Base where
import           Control.Monad (ap, liftM2)
import           Prelude       hiding (fail, (||))
import           Pretty

-------------
-- program --
-------------
data Prog sig a = Return a | Op (sig (Prog sig a))
  deriving Functor

instance Functor sig => Applicative (Prog sig) where
  pure = return
  (<*>) = ap

instance (Functor sig, Applicative (Prog sig)) => Monad (Prog sig) where
  return x = Return x
  Return x >>= f = f x
  Op op    >>= f = Op (fmap (>>= f) op)

--------------------------
-- combining signatures --
--------------------------
data (sig1 :+: sig2) cnt = Inl (sig1 cnt) | Inr (sig2 cnt)
  deriving (Functor, Show)
infixr 6 :+:

instance (Show (sig1 a), Show (sig2 a)) => (Pretty ((:+:) sig1 sig2 a)) where
  pretty x = let r = case x of
                       (Inl z) -> show z
                       (Inr z) -> show z
             in if isPared r then r else par r
    where
      isPared :: String -> Bool
      isPared (c:cs) | c == '(' && last cs == ')' = True
      isPared _      = False

      par :: String -> String
      par s = "(" ++ s ++ ")"

      remPar :: String -> String
      remPar s = case (s, reverse s) of
                   ('(' : '(' : s', ')' : ')' : _) -> par (remPar s')
                   _                               -> s

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

----------------------
-- helper functions --
----------------------
inject :: (sub :<: sup) => sub (Prog sup a) -> Prog sup a
inject = Op . inj

project :: (sub :<: sup) => Prog sup a -> Maybe (sub (Prog sup a))
project (Op s) = prj s
project _      = Nothing

-----------------
-- Void effect --
-----------------
data Void cnt
  deriving Functor

instance (Show (Void a)) where
  show = undefined

run :: Prog Void a -> a
run (Return x) = x

------------------
-- State effect --
------------------
data State s cnt = Get' (s -> cnt)
                 | Put' s cnt
  deriving Functor

pattern Get k <- (project -> Just (Get' k))

get :: (State s :<: sig) => Prog sig s
get = inject (Get' return)

pattern Put s k <- (project -> Just (Put' s k))

put :: (State s :<: sig) => s -> Prog sig ()
put s = inject (Put' s (return ()))

runState :: Functor sig => s -> Prog (State s :+: sig) a -> Prog sig (s, a)
runState s (Return a) = return (s, a)
runState s (Get    k) = runState s (k s)
runState s (Put s' k) = runState s' k
runState s (Other op) = Op (fmap (runState s) op)

-------------------
-- other effects --
-------------------
pattern Other s = Op (Inr s)
