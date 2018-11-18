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

module Once where

import           Control.Monad.Identity hiding (fail)
import           ExceptionsHO
import           HO
import           Prelude                hiding (fail, (||))

-- HNondet
----------
data HNondet m a = Fail' | m a :|* m a
  deriving Functor

instance HFunctor HNondet where
  hmap _ Fail'     = Fail'
  hmap t (x :|* y) = t x :|* t y


instance Syntax HNondet where
  emap _ Fail'     = Fail'
  emap f (x :|* y) = f x :|* f y

  handle _ _   Fail'     = Fail'
  handle c hdl (x :|* y) = let handle z = hdl (fmap (const z) c)
                           in handle x :|* handle y

pattern Fail <- (project -> Just Fail')

fail :: (HNondet ⊂ sig) => Prog sig a
fail = inject Fail'

pattern p :|| q <- (project -> Just (p :|* q))

(||) :: (HNondet ⊂ sig) => Prog sig a -> Prog sig a -> Prog sig a
p || q = inject (p :|* q)

-- HCut
-------
data HCut m a = Cutfail' | Call' (m a)
  deriving Functor

instance HFunctor HCut where
  hmap _ Cutfail'  = Cutfail'
  hmap t (Call' p) = Call' (t p)

instance Syntax HCut where
  emap _ Cutfail'  = Cutfail'
  emap f (Call' p) = Call' (f p)

  handle _ _   Cutfail'  = Cutfail'
  handle c hdl (Call' p) = Call' (hdl (fmap (const p) c))

pattern Cutfail <- (project -> Just Cutfail')

cutfail :: (HCut ⊂ sig) => Prog sig a
cutfail = inject Cutfail'

pattern Call p <- (project -> Just (Call' p))

call :: (HCut ⊂ sig) => Prog sig a -> Prog sig a
call p = inject $ Call' p

runCut :: forall sig a. (Syntax sig, HNondet ⊂ sig) => Prog (HCut + sig) a
     -> Prog sig (Identity a)
runCut (Return a)  = fmap Identity (return a)
runCut Fail        = fail
runCut Cutfail     = fail
runCut (Call p)    = go p fail
  where
    go :: Prog (HCut + sig) a -> Prog sig a -> Prog sig (Identity a)
    go (Return a ) q = fmap Identity $ return a || q
    go (Fail     ) q = fmap Identity $ q
    go (Cutfail  ) q = fmap Identity $ fail
    go (Call p)    q = go p q
    go (p1 :|| p2) q = go p1 (fmap runIdentity $ go p2 q)
    go (Other op ) q = Op (handle (Identity ()) hdl op)
      where hdl imx = runCut (runIdentity imx) -- Still throws away q
runCut (p1 :|| p2) = runCut p1 || runCut p2
runCut (Other op)  = Op (handle (Identity ()) hdl op)
  where hdl imx = runCut (runIdentity imx)

cut :: (HNondet ⊂ sig, HCut ⊂ sig) => Prog sig ()
cut = skip || cutfail

skip :: Monad m => m ()
skip = return ()

once :: (HNondet ⊂ sig) => Prog (HCut + sig) b -> Prog sig b
once p = fmap runIdentity . runCut $
  do call $ do
       x <- p
       cut
       return x

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

coin :: (HNondet ⊂ sig) => Prog sig Bool
coin = return True || return False

e10 = (run . solutions . runCut) $
  call $ do
    b <- coin
    cut
    return b || return b

e11 = (run . solutions . runCut) $ do
  b <- (call $ do b <- coin
                  cut
                  return b)
  (return b || return b)

e12 :: [(Int, Identity Int)]
e12 = (run . solutions . runState 0 . runCut) $ do
 call $ do
  put (1 :: Int) || put (2 :: Int)
  put (3 :: Int) || put (4 :: Int)
  get
