{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE ViewPatterns       #-}

module CallTimeChoice where
import           Code          hiding (Fail, Nondet (..), fail)
import           Prelude       hiding (fail)

import           Control.Monad (liftM2)

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

runShare :: (Functor sig, ND ⊂ sig) => Int -> Prog (Share + sig) a -> (Prog sig a)
runShare i p = bshare i p

bshare :: (ND ⊂ sig) => Int -> Prog (Share + sig) a -> Prog sig a
bshare _ (Return a) = return a
bshare i (BShare p)  = eshare i p >>= bshare i
bshare _ (EShare p)  = error "Mismatched Eshare!"
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

p :: Prog (Share + ND + Void) Bool
p = do
  b <- share' (choice (return True) (return False))
  choice (return b) (return b)

e :: [Bool]
e = snd . run . runND [] . runShare 0 $ p
