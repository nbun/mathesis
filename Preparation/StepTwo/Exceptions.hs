{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

module Exceptions where

import           Code
import           Prelude hiding (fail, (||))

data Exc e cnt = Throw' e
  deriving Functor

pattern Throw e <- (project -> Just (Throw' e))

throw :: (Exc e ⊂ sig) => e -> Prog sig a
throw e = inject (Throw' e)

runExc :: Functor sig => Prog (Exc e + sig) a -> Prog sig (Either e a)
runExc (Return x) = return (Right x)
runExc (Throw e)  = return (Left e)
runExc (Other op) = Op (fmap runExc op)

catch :: (Exc e ⊂ sig) => Prog sig a -> (e -> Prog sig a) -> Prog sig a
catch (Return x) h = return x
catch (Throw e) h  = h e
catch (Op op) h    = Op (fmap (\p -> catch p h) op)

tripleDecr :: (State Int ⊂ sig, Exc () ⊂ sig) => Prog sig ()
tripleDecr = decr >> catch (decr >> decr) return

decr :: (State Int ⊂ sig, Exc () ⊂ sig) => Prog sig ()
decr = do x <- get
          if x > (0 :: Int) then put (pred x) else throw ()

e7 :: Either () (Int, ())
e7 = (run . runExc . runState 2) tripleDecr
