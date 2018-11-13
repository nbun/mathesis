{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Scoped where

import Prelude hiding (fail, (||))
import Code
import Grammar

data Call cnt = BCall' cnt | ECall' cnt
  deriving Functor

pattern BCall p <- (project -> Just (BCall' p))
pattern ECall p <- (project -> Just (ECall' p))

call' :: (Call ⊂ sig) => Prog sig a -> Prog sig a
call' p = do begin ; x <- p ; end ; return x
  where
    begin = inject (BCall' (return ()))
    end   = inject (ECall' (return ()))

expr3 :: (Nondet ⊂ sig, Symbol ⊂ sig, Call ⊂ sig, Cut ⊂ sig) => Prog sig Int
expr3 = do i <- term
           call' (do symbol '+'; cut; j <- expr; return (i + j)
                   || do return i)

e6 = run . solutions . runCut . parse "1" $ expr3

runCut :: (Nondet ⊂ sig) => Prog (Call + Cut + sig) a -> Prog sig a
runCut p = call (bcall p)

bcall :: (Nondet ⊂ sig) => Prog (Call + Cut + sig) a -> Prog (Cut + sig) a
bcall (Return a) = return a
bcall (BCall p) = upcast (call (ecall p)) >>= bcall
bcall (ECall p) = error "Mismatched ECall!"
bcall (Other op) = Op (fmap bcall op)

ecall :: (Nondet ⊂ sig) => Prog (Call + Cut + sig) a -> Prog (Cut + sig) (Prog (Call + Cut + sig) a)
ecall (Return a) = return (Return a)
ecall (BCall p) = upcast (call (ecall p)) >>= ecall
ecall (ECall p) = return p
ecall (Other op) = Op (fmap ecall op)

upcast :: (Functor f , Functor sig) => Prog sig a -> Prog (f + sig) a
upcast (Return x) = return x
upcast (Op op) = Op (Inr (fmap upcast op))

e65 = (run . solutions . runCut) (once
 ((||) (return True) (return False) >>= \b -> cut >> return b))

e651 = (run . solutions . runCut) (once
 (call' $ (||) (return True) (return False) >>= \b -> cut >> return b))


e66 = (run . solutions . runCut) (once
 ((||) (return True) (return False) >>= \b -> cut >> (return b || return b)))


e661 = (run . solutions . runCut) (once
 (call' $ (||) (return True) (return False) >>= \b -> cut >> (return b || return b)))


e662 = (run . solutions . runCut) (once
 (call' $ (||) (return True) (return False) >>= \b -> cut >> (return b))
 >>= \b -> return b)
