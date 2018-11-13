{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ScopedRevisited where

import Prelude hiding (fail, (||))
import Code
import Scoped
import Exceptions

data Catch e cnt = BCatch' cnt (e -> cnt) | ECatch' cnt
  deriving Functor

pattern BCatch p q <- (project -> Just (BCatch' p q))
pattern ECatch p <- (project -> Just (ECatch' p))

catch' :: forall sig e a . (Catch e ⊂ sig) => Prog sig a -> (e -> Prog sig a) -> Prog sig a
catch' p h = begin (do x <- p; end; return x) h where
  begin p q = inject (BCatch' p q)
  end = inject (ECatch' (return ()) :: Catch e (Prog sig ()))

runCatch :: (Functor sig) => Prog (Catch e + (Exc e + sig)) a -> Prog sig (Either e a)
runCatch p = runExc (bcatch p)

bcatch :: forall sig e a. (Functor sig) => Prog (Catch e + (Exc e + sig)) a -> Prog (Exc e + sig) a
bcatch (Return a) = return a
bcatch (BCatch p q) = do r <- upcast (runExc (ecatch p))
                         (bcatch . either q id) r
-- bcatch (Other op) = Op (fmap bcatch op)
bcatch p | Just (ECatch' p :: Catch e (Prog (Catch e1 + (Exc e1 + sig)) a ))
           <- project p = error "bla"
bcatch (Other op) = Op (fmap bcatch op)

------------------------------------------
ecatch :: forall sig e a. (Functor sig) => Prog (Catch e + (Exc e + sig)) a
       -> Prog (Exc e + sig) (Prog (Catch e + (Exc e + sig)) a)
ecatch (Return a) = return (Return a)
ecatch (BCatch p q) = do r <- upcast (runExc (ecatch p))
                         (ecatch . either q id) r
-- ecatch (ECatch p) = return p
ecatch p | Just (ECatch' p :: Catch e (Prog (Catch e1 + (Exc e1 + sig)) a ))
           <- project p = return p
ecatch (Other op) = Op (fmap ecatch op)

--                                                    is missing in the paper
--                                                    |
--                                                    v
tripleDecr' :: (State Int ⊂ sig, Exc () ⊂ sig, Catch () ⊂ sig) => Prog sig ()
tripleDecr' = decr >> catch' (decr >> decr) return

e8 :: Either () (Int, ())
e8 = (run . runCatch . runState 2) tripleDecr' -- Evaluates to Right (0,()), should be Right (1, ())

e9 :: (Int, Either () ())
e9 = (run . runState 2 . runCatch) tripleDecr'

e10 :: Either () (Int, ())
e10 = (run . runCatch . runState 0) (put (42 :: Int) >> return ())

e11 :: Either () (Int, ())
e11 = (run . runCatch . runState 0) (throw ())

-- e12 :: Either () (Int, ())
-- e12 = (run . runCatch . runState 0) test

-- test :: (State Int ⊂ sig, Exc () ⊂ sig, Catch () ⊂ sig) => Prog sig ()
-- test = (catch (throw ()) (\(e :: ()) -> put (42 :: Int) >> return ()))
