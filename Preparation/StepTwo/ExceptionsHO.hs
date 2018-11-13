{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

module ExceptionsHO where

import Prelude hiding (fail, (||))
import Code (State(..))
import HO

-- HState
---------
type HState s = Lift (State s)

pattern Get k <- (project -> Just (Lift (Get' k)))

get :: (HState s ⊂ sig) => Prog sig s
get = inject (Lift (Get' return))

pattern Put s k <- (project -> Just (Lift (Put' s k)))

put :: (HState s ⊂ sig) => s -> Prog sig ()
put s = inject (Lift (Put' s (return ())))

runState :: Syntax sig => s -> Prog (HState s + sig) a -> Prog sig (s, a)
runState s (Return a) = return (s, a)
runState s (Get k) = runState s (k s)
runState s (Put s' k) = runState s' k
runState s (Other op) = Op (handle (s, ()) (uncurry runState) op)


-- HExc
-------
data HExc e m a = Throw' e
                | forall x . Catch' (m x) (e -> m x) (x -> m a)

instance Functor m => Functor (HExc e m) where
  fmap f (Throw' e) = Throw' e
  fmap f (Catch' p h k) = Catch' p h (fmap f . k)

instance HFunctor (HExc e) where
  hmap t (Throw' x) = Throw' x
  hmap t (Catch' p h k) = Catch' (t p) (t . h) (t . k)

instance Syntax (HExc e) where
  emap f (Throw' e) = Throw' e
  emap f (Catch' p h k) = Catch' p h (f . k)

  handle c hdl (Throw' x) = Throw' x
  handle c hdl (Catch' p h k) = Catch' (hdl (fmap (const p) c))
    (\e -> hdl (fmap (const (h e)) c))
    (hdl . fmap k)

pattern Throw e <- (project -> Just (Throw' e))

throw :: (HExc e ⊂ sig) => e -> Prog sig a
throw e = inject (Throw' e)

pattern Catch p h k <- (project -> Just (Catch' p h k))

catch :: (HExc e ⊂ sig) => Prog sig a -> (e -> Prog sig a) -> Prog sig a
catch p h = inject (Catch' p h return)

runExc :: Syntax sig => Prog (HExc e + sig) a -> Prog sig (Either e a)
runExc (Return x) = return (Right x)
runExc (Throw x) = return (Left x)
runExc (Catch p h k) =
  do r <- runExc p
     case r of
       Left e -> do r <- runExc (h e)
                    case r of
                      Left e -> return (Left e)
                      Right a -> runExc (k a)
       Right a -> runExc (k a)

runExc (Other op) = Op (handle (Right ()) hdl op)
  where hdl :: Syntax sig => (forall x. Either e (Prog (HExc e + sig) x)
            -> Prog sig (Either e x))
        hdl = either (return . Left) runExc

tripleDecr :: (HState Int ⊂ sig, HExc () ⊂ sig) => Prog sig ()
tripleDecr = decr >> (catch (decr >> decr) return)

decr :: (HState Int ⊂ sig, HExc () ⊂ sig) => Prog sig ()
decr = do x <- get
          if x > (0 :: Int) then put (pred x) else throw ()

e7 :: Either () (Int, ())
e7 = (run . runExc . runState 2) tripleDecr

e8 :: (Int, Either () ())
e8 = (run . runState 2 . runExc) tripleDecr
