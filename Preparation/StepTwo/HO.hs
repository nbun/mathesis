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

instance {-# OVERLAPPING #-} (Syntax sig1, Syntax sig2) => sig1 ⊂ (sig1 + sig2) where
  inj = Inl
  prj (Inl fa) = Just fa
  prj _        = Nothing

instance {-# OVERLAPPABLE #-} (Syntax sig1, sig ⊂ sig2) => sig ⊂ (sig1 + sig2) where
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

data Nondet cnt = Fail' | cnt :|* cnt
  deriving Functor

type HNondet = Lift Nondet

inject :: (sub ⊂ sup) => sub (Prog sup) a -> Prog sup a
inject = Op . inj

project :: (sub ⊂ sup) => Prog sup a -> Maybe (sub (Prog sup) a)
project (Op s) = prj s
project _      = Nothing

pattern Fail <- (project -> Just (Lift Fail'))

fail :: (HNondet ⊂ sig) => Prog sig a
fail = inject $ Lift Fail'

pattern p :|| q <- (project -> Just (Lift (p :|* q)))

(||) :: (HNondet ⊂ sig) => Prog sig a -> Prog sig a -> Prog sig a
p || q = inject $ Lift (p :|* q)

pattern Other s = Op (Inr s)

data Cut cnt = Cutfail'
  deriving Functor

type HCut = Lift Cut

pattern Cutfail <- (project -> Just (Lift Cutfail'))

cutfail :: (HCut ⊂ sig) => Prog sig a
cutfail = inject $ Lift Cutfail'

call :: forall sig a. (Syntax sig, HNondet ⊂ sig) => Prog (HCut + sig) a
     -> Prog sig (Identity a)
call p = go p fail
  where
    go :: Prog (HCut + sig) a -> Prog sig a -> Prog sig (Identity a)
    go (Return a ) q = fmap Identity $ return a || q
    go (Fail     ) q = fmap Identity $ q
    go (Cutfail  ) q = fmap Identity $ fail
    go (p1 :|| p2) q = go p1 (fmap runIdentity $ go p2 q)
    go (Other op ) q = Op (handle (Identity ()) hdl op)

    hdl :: (forall x. Identity (Prog (HCut + sig) x) -> Prog sig (Identity x))
    hdl imx = call (runIdentity imx)

cut :: (HNondet ⊂ sig, HCut ⊂ sig) => Prog sig ()
cut = skip || cutfail

skip :: Monad m => m ()
skip = return ()

once :: (HNondet ⊂ sig) => Prog (HCut + sig) b -> Prog sig b
once p = fmap runIdentity $ call
  (do
    x <- p
    cut
    return x
  )

data Void cnt
  deriving Functor

type HVoid = Lift Void

run :: Prog HVoid a -> a
run (Return x) = x

solutions :: forall sig a. (Syntax sig) => Prog (HNondet + sig) a
          -> Prog sig [a]
solutions (Return a) = return [a]
solutions Fail       = return []
solutions (p :|| q ) = liftM2 (++) (solutions p) (solutions q)
solutions (Other op) = Op (handle [()] hdl op)
  where hdl :: (forall x. [Prog (HNondet + sig) x] -> Prog sig [x])
        hdl []     = return []
        hdl (p:ps) = liftM2 (++) (solutions p) (hdl ps)

e3 :: [[Int]]
e3 = (run . solutions . once) (knapsack' 3 [3, 2, 1])

knapsack' :: (HNondet ⊂ sig) => Int -> [Int] -> Prog sig [Int]
knapsack' w vs
  | w < 0 = fail
  | w == 0 = return []
  | w > 0 = do
    v   <- select' vs
    vs' <- knapsack' (w - v) vs
    return (v : vs')

select' :: (HNondet ⊂ sig) => [a] -> Prog sig a
select' = foldr (||) fail . map return
