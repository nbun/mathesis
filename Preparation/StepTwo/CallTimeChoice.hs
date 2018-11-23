{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}

module CallTimeChoice where
import           Code                hiding (Fail, Nondet (..), fail)
import           Prelude             hiding (fail)
import           Tree

import           Control.Applicative (Alternative (..))
import           Control.Monad       (MonadPlus (..), liftM2)


toTree :: Prog (ND + Void) a -> Tree a
toTree Fail               = F
toTree (Choice mID t1 t2) = C mID (toTree t1) (toTree t2)
toTree (Return x)         = L x

-- Nondeterminism
-----------------

data ND cnt = Fail' | Choice' (Maybe Int) cnt cnt
  deriving (Functor, Show)

pattern Fail <- (project -> Just Fail')
pattern Choice m p q <- (project -> Just (Choice' m p q))

fail :: (ND ⊂ sig) => Prog sig a
fail = inject Fail'

choice :: (ND ⊂ sig) => Prog sig a -> Prog sig a -> Prog sig a
choice p q = inject (Choice' Nothing p q)

choiceID :: (ND ⊂ sig) => Maybe Int -> Prog sig a -> Prog sig a -> Prog sig a
choiceID m p q = inject (Choice' m p q)

data Choice = CLeft | CRight
type Choices = [(Int, Choice)]

runND :: (Functor sig) => Choices -> Prog (ND + sig) a -> Prog sig (Choices, [a])
runND cs (Return a) = return (cs, [a])
runND cs Fail       = return (cs, [])
runND cs (Choice Nothing p q ) = do
  (_, xs) <- runND cs p
  (_, ys) <- runND cs q
  return (cs, (xs ++ ys))
runND cs (Choice (Just i) p q) = case lookup i cs of
                                   Just CLeft  -> runND cs p
                                   Just CRight -> runND cs q
                                   Nothing     -> do
                                     (_, xs) <- runND ((i, CLeft):cs) p
                                     (_, ys) <- runND ((i, CRight):cs) q
                                     return (cs, xs ++ ys)
runND cs (Other op) = Op (fmap (runND cs) op)

-- Sharing
----------

data Share cnt = BShare' Int cnt | EShare' Int cnt
  deriving (Functor, Show)

pattern BShare i p <- (project -> Just (BShare' i p))
pattern EShare i p <- (project -> Just (EShare' i p))

share' :: (Share ⊂ sig, State Int ⊂ sig) => Prog sig a -> Prog sig a
share' p = do i <- get
              put (i + 1)
              begin i
              x <- p
              end i
              return x
  where
    begin i = inject (BShare' i (return ()))
    end   i = inject (EShare' i (return ()))

instance (Share ⊂ sig, State Int ⊂ sig, ND ⊂ sig) => Sharing (Prog sig) where
  share p = do i <- get
               put (i + 1)
               return $ sharen' i p

sharen' :: (Share ⊂ sig) => Int -> Prog sig a -> Prog sig a
sharen' n p = do begin n
                 x <- p
                 end n
                 return x
  where
    begin i = inject (BShare' i (return ()))
    end   i = inject (EShare' i (return ()))

sharen :: (Share ⊂ sig, State Int ⊂ sig) => Int -> Prog sig a -> Prog sig (Prog sig a)
sharen n = return . sharen' n

runShare :: (Functor sig, ND ⊂ sig)
         => Int -> Prog (Share + sig) a -> (Prog sig a)
runShare = bshare

bshare :: (ND ⊂ sig)
       => Int -> Prog (Share + sig) a -> Prog sig a
bshare _ (Return a)   = return a
bshare _ (BShare i p) = eshare i p >>= bshare i
bshare _ (EShare _ p) = error "Mismatched Eshare!"
bshare i (Other op)   = Op (fmap (bshare i) op)

eshare :: (ND ⊂ sig)
       => Int -> Prog (Share + sig) a -> Prog sig (Prog (Share + sig) a)
eshare _ (Return a) = return (Return a)
eshare _ (BShare i p)  = eshare i p
eshare i (EShare j p)  | i == j = return p
                       | otherwise = eshare (i-1) p
eshare _ Fail          = fail
eshare i (Choice Nothing p q) = do
  p' <- eshare (2 * i) p
  q' <- eshare (2 * i + 1) q
  return $ choiceID (Just i) p' q'
eshare i (Choice (Just _) _ _) = error "Choice already shared!"
eshare i (Other op) = Op (fmap (eshare i) op)

-- Examples
-----------

deriving instance Show a => Show (Prog (Share + ND + Void) a)
deriving instance Show a => Show (Prog (ND + Void) a)

xor :: Monad m => m Bool -> m Bool -> m Bool
xor fb1 fb2 = fb1 >>= \b1 -> fb2 >>= \b2 -> case (b1,b2) of
                                              (True,True)   -> return False
                                              (False,False) -> return False
                                              _             -> return True

orM :: MonadPlus m => m Bool -> m Bool -> m Bool
orM fb1 fb2 = fb1 >>= \b1 -> case b1 of
                               True -> return True
                               _    -> fb2

coin :: MonadPlus m => m Bool
coin = return True `mplus` return False

runCurry :: Prog (State Int + Share + ND + Void) a -> [a]
runCurry = map snd . snd.  run . runND [] . runShare 1 . runState 1

runTree :: (Pretty a, Show a) => Prog (State Int + Share + ND + Void) a -> IO ()
runTree = putStrLn . pretty . toTree . runShare 1 . runState 1

instance (Functor sig, ND ⊂ sig) => Alternative (Prog sig) where
  empty = fail
  (<|>) = choice

instance (Functor sig, ND ⊂ sig) => MonadPlus (Prog sig) where
  mplus = choice
  mzero = fail

class (MonadPlus m) => Sharing m where
  share :: m a -> m (m a)

example1, example2 :: MonadPlus m => m Bool
example1 = coin
example2 = mplus coin coin

example3 :: Prog (State Int + Share + ND + Void) Bool
example3 = share coin >>= \fx -> mplus fx fx

exOr0, exOr1 :: MonadPlus m => m Bool
exOr0 = orM coin (return False)
exOr1 = orM coin coin

exOr2, exOr2a, exOr2b :: Prog (State Int + Share + ND + Void) Bool
exOr2  = share coin >>= \fx -> orM fx fx
exOr2a = share coin >>= \fx -> orM (return False) (orM fx fx)
exOr2b = share coin >>= \fx -> orM (return True) (orM fx fx)


exOr3, exOr3a, exOr3b, exOr3c :: MonadPlus m => m Bool
exOr3 = orM (mplus coin coin) (return True)
exOr3a = orM (mplus coin coin) coin
exOr3b = orM coin (mplus coin coin)
exOr3c = orM (mplus coin coin) (mplus coin coin)

-- here we share, even though nothing is shared
exOr4, exOrShare :: Prog (State Int + Share + ND + Void) Bool
exOr4     = share coin >>= \fx -> orM fx coin
exOrShare = share coin >>= \fx -> orM coin fx


exOr6, exOr7, exOr7a, exOr7b :: Prog (State Int + Share + ND + Void) Bool
exOr6  = share coin >>= \fx -> orM fx (orM fx coin)
exOr7  = share coin >>= \fx -> orM coin (orM fx fx)
exOr7a = share coin >>= \fx -> orM (return True) (orM fx fx)
exOr7b = share coin >>= \fx -> orM (return False) (orM fx fx)


exShareConst, exShareConstOrR, exShareConstOrL, exShareConstOrR2, exOrShareShare,
  exOrShareShare2, exOrShareShare3, exOrShareNested,
  exOrShareId :: Prog (State Int + Share + ND + Void) Bool
exShareConst     = share coin >>= \fx -> const fx fx
exShareConstOrR  = share coin >>= \fx -> orM fx (const fx fx)
exShareConstOrL  = share coin >>= \fx -> orM (const fx fx) fx
exShareConstOrR2 = share coin >>= \fx -> orM (return True) (const fx fx)
exOrShareShare   = share coin >>= \fx ->
                   share coin >>= \fy ->
                   orM fx (orM fy (orM fx fy))
exOrShareShare2  = share (coin `mplus` coin) >>= \fx ->
                   orM fx fx
exOrShareShare3= share (coin `mplus` coin `mplus` coin `mplus` coin) >>= \fx ->
                   orM fx fx
exOrShareId      = share coin >>= id

exOrShareNested  = share coin >>= \fx ->
                   orM fx (share coin >>= \fy ->
                               orM fy (orM fx fy))

exFailed, exSkipIds, exLoop, exLoop2, exRepeatedShare, exShareIgnoreShare
  :: (Monad m, Sharing m) => m Bool
exFailed  = share (mzero :: MonadPlus m => m Bool) >>= \fx -> const (return True) fx
exSkipIds = share coin >>= \fx -> const coin (const fx fx)
exLoop  = let loop :: m ()
              loop = loop in share loop >>= \fx -> const (return True) (const fx fx)
exLoop2 = let loop :: m ()
              loop = loop in share loop >>= \fx -> const coin (const fx fx)
exRepeatedShare = share coin >>= \fx -> share fx >>= \fy -> orM fy fy
exShareIgnoreShare =
  share coin >>= \fx -> const (return True) (share fx >>= \fy -> orM fy fy)

data PairM m a = PairM (m a) (m a)

pairM :: Monad m => m a -> m a -> m (PairM m a)
pairM fx fy = return $ PairM fx fy

dup :: Monad m => m a -> m (PairM m a)
dup fx = pairM fx fx

dupShare :: (Monad m, Sharing m) => m a -> m (PairM m a)
dupShare fx = share fx >>= \fx' -> dup fx'

exDup :: (MonadPlus m) => m (PairM m Bool)
exDup = dup coin

exDupShare :: (MonadPlus m, Sharing m) => m (PairM m Bool)
exDupShare = dupShare coin

