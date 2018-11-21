{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE ViewPatterns       #-}

module CallTimeChoice where
import           Code                hiding (Fail, Nondet (..), fail)
import           Prelude             hiding (fail)

import           Control.Applicative (Alternative (..))
import           Control.Monad       (MonadPlus (..), liftM2)

data Tree a = F
            | L a
            | C (Maybe Int) (Tree a) (Tree a)
  deriving Show

class Pretty a where
  pretty :: a -> String
  pretty' :: a -> Int -> String

instance Pretty Bool where
  pretty = show

instance Pretty a => Pretty (Tree a) where
  pretty t = pretty' t 0
   where
    pretty' F _ = "_|_"
    pretty' (L x) _ = pretty x
    pretty' (C n t1 t2) wsp =
      show n ++ "\n" ++ replicate wsp ' ' ++ "|---- " ++ pretty' t1 (wsp+6)
             ++ "\n" ++ replicate wsp ' ' ++ "|---- " ++ pretty' t2 (wsp+6)

toTree :: Prog (ND + Void) a -> Tree a
toTree Fail               = F
toTree (Choice mID t1 t2) = C mID (toTree t1) (toTree t2)
toTree (Return x)         = L x

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

data Share cnt = BShare' cnt | EShare' cnt
  deriving (Functor, Show)

pattern BShare p <- (project -> Just (BShare' p))
pattern EShare p <- (project -> Just (EShare' p))

share' :: (Share ⊂ sig) => Prog sig a -> Prog sig a
share' p = do begin ; x <- p ; end ; return x
  where
    begin = inject (BShare' (return ()))
    end   = inject (EShare' (return ()))

share :: (Share ⊂ sig) => Prog sig a -> Prog sig (Prog sig a)
share = return . share'


runShare :: (Functor sig, ND ⊂ sig) => Int -> Prog (Share + sig) a -> (Prog sig a)
runShare i p = bshare i p

bshare :: (ND ⊂ sig) => Int -> Prog (Share + sig) a -> Prog sig a
bshare _ (Return a) = return a
bshare i (BShare p) = eshare i p >>= bshare i
bshare _ (EShare p) = error "Mismatched Eshare!"
bshare i (Other op) = Op (fmap (bshare i) op)

eshare :: (ND ⊂ sig) => Int -> Prog (Share + sig) a -> Prog sig (Prog (Share + sig) a)
eshare _ (Return a) = return (Return a)
eshare i (BShare p)  = eshare i p
eshare _ (EShare p)  = return p
eshare _ Fail        = fail
eshare i (Choice Nothing p q) = do
  p' <- eshare (2 * i) p
  q' <- eshare (2 * i + 1) q
  return $ choiceID (Just i) p' q'
eshare i (Choice (Just _) _ _) = error "Choice already shared!"
eshare i (Other op) = Op (fmap (eshare i) op)

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

p :: Prog (Share + ND + Void) Bool
p = do
  b <- share' (choice (return True) (return False))
  xor (return b) (return b)

e :: [Bool]
e = snd . run . runND [] . runShare 0 $ p


runCurry :: Prog (Share + ND + Void) a -> [a]
runCurry = snd . run . runND [] . runShare 0

instance Alternative (Prog (Share + ND + Void))
instance MonadPlus (Prog (Share + ND + Void)) where
  mplus =  choice
  mzero = fail

instance Functor sig => Alternative (Prog (ND + sig))
instance Functor sig => MonadPlus (Prog (ND + sig)) where
  mplus =  choice
  mzero = fail


example1 :: MonadPlus m => m Bool
example1 = coin
example2 :: MonadPlus m => m Bool
example2 = mplus coin coin
example3 :: Prog (Share + ND + Void) Bool
example3 = share coin >>= \fx -> mplus fx fx

exOr0 :: MonadPlus m => m Bool
exOr0 = orM coin (return False)

exOr1 :: MonadPlus m => m Bool
exOr1 = orM coin coin
exOr2 :: Prog (Share + ND + Void) Bool
exOr2 = share coin >>= \fx -> orM fx fx
exOr2a :: Prog (Share + ND + Void) Bool
exOr2a = share coin >>= \fx -> orM (return False) (orM fx fx)
exOr2b :: Prog (Share + ND + Void) Bool
exOr2b = share coin >>= \fx -> orM (return True) (orM fx fx)


exOr3 :: MonadPlus m => m Bool
exOr3 = orM (mplus coin coin) (return True)
exOr3a :: MonadPlus m => m Bool
exOr3a = orM (mplus coin coin) coin
exOr3b :: MonadPlus m => m Bool
exOr3b = orM coin (mplus coin coin)
exOr3c :: MonadPlus m => m Bool
exOr3c = orM (mplus coin coin) (mplus coin coin)
-- here we share, even though nothing is shared
exOr4 :: Prog (Share + ND + Void) Bool
exOr4 = share coin >>= \fx -> orM fx coin
exOrShare :: Prog (Share + ND + Void) Bool
exOrShare = share coin >>= \fx -> orM coin fx


exOr6 :: Prog (Share + ND + Void) Bool
exOr6 = share coin >>= \fx -> orM fx (orM fx coin)
exOr7 :: Prog (Share + ND + Void) Bool
exOr7 = share coin >>= \fx -> orM coin (orM fx fx)
exOr7a :: Prog (Share + ND + Void) Bool
exOr7a = share coin >>= \fx -> orM (return True) (orM fx fx)
exOr7b :: Prog (Share + ND + Void) Bool
exOr7b = share coin >>= \fx -> orM (return False) (orM fx fx)


exShareConst :: Prog (Share + ND + Void) Bool
exShareConst = share coin >>= \fx -> const fx fx
exShareConstOrR :: Prog (Share + ND + Void) Bool
exShareConstOrR = share coin >>= \fx -> orM fx (const fx fx)
exShareConstOrL :: Prog (Share + ND + Void) Bool
exShareConstOrL = share coin >>= \fx -> orM (const fx fx) fx
exShareConstOrR2 :: Prog (Share + ND + Void) Bool
exShareConstOrR2 = share coin >>= \fx -> orM (return True) (const fx fx)
exOrShareShare :: Prog (Share + ND + Void) Bool
exOrShareShare = share coin >>= \fx ->
                 share coin >>= \fy ->
                 orM fx (orM fy (orM fx fy))
exOrShareNested :: Prog (Share + ND + Void) Bool
exOrShareNested = share coin >>= \fx ->
                  orM fx (share coin >>= \fy ->
                              orM fy (orM fx fy))
{-
exFailed :: (MonadPlus m) => m Bool
exFailed = share (mzero :: MonadPlus m => m Bool) >>= \fx -> const (return True) fx
exSkipIds :: (MonadPlus m) => m Bool
exSkipIds = share coin >>= \fx -> const coin (const fx fx)
exLoop :: m Bool
exLoop = let loop :: m ()
             loop = loop in share loop >>= \fx -> const (return True) (const fx fx)
exLoop2 :: m Bool
exLoop2 = let loop :: m ()
              loop = loop in share loop >>= \fx -> const coin (const fx fx)
exRepeatedShare :: (MonadPlus m) => m Bool
exRepeatedShare = share coin >>= \fx -> share fx >>= \fy -> orM fy fy
exShareIgnoreShare :: (MonadPlus m) => m Bool
exShareIgnoreShare =
  share coin >>= \fx -> const (return True) (share fx >>= \fy -> orM fy fy)
-}
