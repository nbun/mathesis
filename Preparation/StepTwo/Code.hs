{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Code where
import           Control.Monad (ap, liftM2)
import           Prelude       hiding (fail, (||))

data Backtr a = BReturn a
              | BFail
              | Backtr a :| Backtr a
  deriving Functor

instance Applicative Backtr where
  pure = return
  (<*>) = ap

instance Monad Backtr where
  return x = BReturn x
  BReturn a >>= f = f a
  BFail     >>= f = BFail
  (p :| q) >>= f = (p >>= f) :| (q >>= f)

knapsack :: Int -> [Int] -> Backtr [Int]
knapsack w vs
  | w < 0 = BFail
  | w == 0 = return []
  | w > 0 = do
    v   <- select vs
    vs' <- knapsack (w - v) vs
    return (v : vs')

select :: [a] -> Backtr a
select = foldr (:|) BFail . map BReturn

allsols :: Backtr a -> [a]
allsols (BReturn x) = [x]
allsols BFail       = []
allsols (p :| q)    = allsols p ++ allsols q

data Prog sig a = Return a | Op (sig (Prog sig a))
  deriving Functor

instance Functor sig => Applicative (Prog sig) where
  pure = return
  (<*>) = ap

data Nondet cnt = Fail' | cnt :|* cnt
  deriving Functor

instance (Functor sig, Applicative (Prog sig)) => Monad (Prog sig) where
  return v = Return v
  Return v >>= prog = prog v
  Op op >>= prog = Op (fmap (>>= prog) op)

data (sig1 + sig2) cnt = Inl (sig1 cnt) | Inr (sig2 cnt)
  deriving Functor

infixr 0 +

class (Functor sub, Functor sup) => sub ⊂ sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance Functor sig => sig ⊂ sig where
  inj = id
  prj = Just

instance {-# OVERLAPPING #-}
  (Functor sig1, Functor sig2) => sig1 ⊂ (sig1 + sig2) where
  inj = Inl
  prj (Inl fa) = Just fa
  prj _        = Nothing

instance {-# OVERLAPPABLE #-}
  (Functor sig1, sig ⊂ sig2) => sig ⊂ (sig1 + sig2) where
  inj = Inr . inj
  prj (Inr ga) = prj ga
  prj _        = Nothing

inject :: (sub ⊂ sup) => sub (Prog sup a) -> Prog sup a
inject = Op . inj

project :: (sub ⊂ sup) => Prog sup a -> Maybe (sub (Prog sup a))
project (Op s) = prj s
project _      = Nothing

pattern Fail <- (project -> Just Fail')

fail :: (Nondet ⊂ sig) => Prog sig a
fail = inject Fail'

pattern p :|| q <- (project -> Just (p :|* q))

(||) :: (Nondet ⊂ sig) => Prog sig a -> Prog sig a -> Prog sig a
p || q = inject (p :|* q)

data Void cnt
  deriving Functor

run :: Prog Void a -> a
run (Return x) = x

pattern Other s = Op (Inr s)

solutions :: (Functor sig) => Prog (Nondet + sig) a -> Prog sig [a]
solutions (Return a) = return [a]
solutions Fail       = return []
solutions (p :|| q ) = liftM2 (++) (solutions p) (solutions q)
solutions (Other op) = Op (fmap solutions op)

allsols' :: Prog (Nondet + Void) a -> [a]
allsols' = run . solutions

data State s cnt = Get' (s -> cnt)
                 | Put' s cnt
  deriving Functor

pattern Get k <- (project -> Just (Get' k))

get :: (State s ⊂ sig) => Prog sig s
get = inject (Get' return)

pattern Put s k <- (project -> Just (Put' s k))

put :: (State s ⊂ sig) => s -> Prog sig ()
put s = inject (Put' s (return ()))

runState :: Functor sig => s -> Prog (State s + sig) a -> Prog sig (s, a)
runState s (Return a) = return (s, a)
runState s (Get    k) = runState s (k s)
runState s (Put s' k) = runState s' k
runState s (Other op) = Op (fmap (runState s) op)

runLocal
  :: Functor sig => s -> Prog (State s + Nondet + sig) a -> Prog sig [(s, a)]
runLocal s = solutions . runState s

runGlobal
  :: Functor sig => s -> Prog (Nondet + State s + sig) a -> Prog sig (s, [a])
runGlobal s = runState s . solutions

choices :: (Nondet ⊂ sig, State Int ⊂ sig) => Prog sig a -> Prog sig a
choices (Return a) = return a
choices (Fail    ) = fail
choices (p :|| q ) = incr >> (choices p || choices q)
choices (Op op   ) = Op (fmap choices op)

incr :: (State Int ⊂ sig) => Prog sig ()
incr = get >>= put . (succ :: Int -> Int)

knapsack' :: (Nondet ⊂ sig) => Int -> [Int] -> Prog sig [Int]
knapsack' w vs
  | w < 0 = fail
  | w == 0 = return []
  | w > 0 = do
    v   <- select' vs
    vs' <- knapsack' (w - v) vs
    return (v : vs')

select' :: (Nondet ⊂ sig) => [a] -> Prog sig a
select' = foldr (||) fail . map return

e1 :: (Int, [[Int]])
e1 = (run . runGlobal (0 :: Int) . choices) (knapsack' 3 [3, 2, 1])

e2 :: ([(Int, [Int])])
e2 = (run . runLocal (0 :: Int) . choices) (knapsack' 3 [3, 2, 1])

data Cut cnt = Cutfail'
  deriving Functor

pattern Cutfail <- (project -> Just Cutfail')

cutfail :: (Cut ⊂ sig) => Prog sig a
cutfail = inject Cutfail'

call :: (Nondet ⊂ sig) => Prog (Cut + sig) a -> Prog sig a
call p = go p fail
 where
  go :: (Nondet ⊂ sig) => Prog (Cut + sig) a -> Prog sig a -> Prog sig a
  go (Return a ) q = return a || q
  go (Fail     ) q = q
  go (Cutfail  ) q = fail
  go (p1 :|| p2) q = go p1 (go p2 q)
  go (Other op ) q = Op (fmap (flip go q) op)

cut :: (Nondet ⊂ sig, Cut ⊂ sig) => Prog sig ()
cut = skip || cutfail

skip :: Monad m => m ()
skip = return ()

once :: (Nondet ⊂ sig) => Prog (Cut + sig) b -> Prog sig b
once p = call
  (do
    x <- p
    cut
    return x
  )

e3 :: [[Int]]
e3 = (run . solutions . once) (knapsack' 3 [3, 2, 1])
