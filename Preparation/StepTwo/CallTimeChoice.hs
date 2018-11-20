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

data Share cnt = Share' cnt
  deriving (Functor, Show)

pattern Share p <- (project -> Just (Share' p))

share :: (Share ⊂ sig) => Prog sig a -> Prog sig a
share p = inject (Share' p)

runShare :: (Functor sig, ND ⊂ sig) => Int -> Prog (Share + sig) a -> (Prog sig a)
runShare _ (Return a)     = return a
runShare _ Fail           = fail
runShare i (Choice m p q) = choiceID m (runShare (2 * i) p) (runShare (2 * i + 1) q)
runShare i (Share p) = name p
  where name (Return a)           = return a
        name Fail                 = fail
        name (Choice Nothing p q) = choiceID (Just i) (name p) (name q)
        name (Other op)           = Op $ fmap name op

p :: Prog (Share + ND + Void) Bool
p = do
  b <- share (choice (return True) (return False))
  choice (return b) (return b)

e :: [Bool]
e = snd . run . runND [] . runShare 0 $ p
