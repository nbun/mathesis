Syntax and Semantics for Operations with Scopes is a paper about math stuff
I do not understand for the most part. Monad operations can be categorized into
algebraic and non-algebraic ones. The difference lies in the property that algebraic
operations commute with bind, for example as in `or(1, 5) >>= k = or(k 1, k 5)`.

In the setting of Plotkin and Pretnar, algebraic operations have no semantics by
themselves. Non-algebraic operations are interpreted by means of handlers. Handlers
handle scoping and semantics simultaneously, which can be problematic because
certain interpretations of programs are no longer possible. Therefore, making scope
part of the syntax would allow handler semantics independent of scoping.

[Math stuff]


The addition of scopes to the manifests itself through the constructor `Scope`
and the argument `g`, a functor that represents different kinds of scopes.

```Haskell
data Prog f g a = Var a
  | Op (f (Prog f g a))
  | Scope (g (Prog f g (Prog f g a)))

instance (Functor f , Functor g) ⇒ Monad (Prog f g) where
  return = Var
  Var x >>= f = f x
  Op op >>= f = Op (fmap (>>= f) op)
  Scope sc >>= f = Scope (fmap (fmap (>>= f)) sc)
```

Representing a simple nondeterministic syntactically works in a natural way.

```
data Choice a = Fail | Or a a deriving Functor

data Once a = Once a deriving Functor

type NDProg = Prog Choice Once

example4 :: NDProg Int
example4 = do x ← once (or (return 1) (return 5))
              or (return x) (return (x + 1))
```

Interpreting the syntax, however, requires some unwieldy data types to encode
the logic. The approach also works for a state monad with scopes variable
bindings and a concurrency model.
