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

module Grammar where
import           Code
import           Prelude hiding (fail, (||))

data Symbol cnt = Symbol' Char (Char -> cnt)
  deriving Functor

pattern Symbol c k <- (project -> Just (Symbol' c k))

symbol :: (Symbol <: sig) => Char -> Prog sig Char
symbol c = inject (Symbol' c return)

digit :: (Nondet <: sig, Symbol <: sig) => Prog sig Char
digit = foldr (||) fail (fmap symbol ['0'..'9'])

many, many1 :: (Nondet <: sig) => Prog sig a -> Prog sig [a]
many p = many1 p || return []
many1 p = do a <- p; as <- many p; return (a : as)

parse :: (Nondet <: sig) => [Char ] -> Prog (Symbol + sig) a -> Prog sig a
parse []       (Return a) = return a
parse (x : xs) (Return a) = fail
parse []       (Symbol c k) = fail
parse (x : xs) (Symbol c k) | x == c = parse xs (k x)
                            | otherwise = fail
parse xs       (Other op) = Op (fmap (parse xs) op)

expr :: (Nondet <: sig, Symbol <: sig) => Prog sig Int
expr = do i <- term; symbol '+'; j <- expr; return (i + j)
    || do i <- term; return i

term :: (Nondet <: sig, Symbol <: sig) => Prog sig Int
term = do i <- factor; symbol '*'; j <- term; return (i * j)
    || do i <- factor; return i

factor :: (Nondet <: sig, Symbol <: sig) => Prog sig Int
factor = do ds <- many1 digit; return (read ds)
      || do symbol '('; i <- expr; symbol ')'; return i

e4 = (allsols' . parse "2+8*5") expr

expr1 :: (Nondet <: sig, Symbol <: sig) => Prog sig Int
expr1 = do i <- term
           (do symbol '+'; j <- expr1; return (i + j)
            || do return i)

expr2 :: (Nondet <: sig, Symbol <: sig) => Prog sig Int
expr2 = do i <- term
           call (do symbol '+'; cut; j <- expr2; return (i + j)
                 || do return i)

e5 = (allsols' . parse "1") expr2

