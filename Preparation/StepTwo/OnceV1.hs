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

module OnceV1 where
import           Control.Monad          (ap, liftM2)
import           Control.Monad.Identity hiding (fail)
import           ExceptionsHO
import           HO
import           Prelude                hiding (fail, (||))

data Nondet cnt = Fail' | cnt :|* cnt
  deriving Functor

type HNondet = Lift Nondet

pattern Fail <- (project -> Just (Lift Fail'))

fail :: (HNondet ⊂ sig) => Prog sig a
fail = inject $ Lift Fail'

pattern p :|| q <- (project -> Just (Lift (p :|* q)))

(||) :: (HNondet ⊂ sig) => Prog sig a -> Prog sig a -> Prog sig a
p || q = inject $ Lift (p :|* q)

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

e12 :: [(Int, Identity Int)]
e12 = (run . solutions . runState 0 . call) $ do
  put (1 :: Int) || put (2 :: Int)
  put (3 :: Int) || put (4 :: Int)
  get
