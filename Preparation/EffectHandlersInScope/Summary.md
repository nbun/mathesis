Effect Handlers in Scope is a paper about expressing the semantics of effects and
scope by means of handlers. The core data structure used throughout the paper is
`Prog`.

```Haskell
data Prog sig a = Return a              -- pure computations 
                | Op (sig (Prog sig a)) -- impure computations
                
instance (Functor sig) => Monad (Prog sig) where
  return v = Return v
  
  Return v >>= prog = prog v
  Op op    >>= prog = Op (fmap (>>= prog) op)
```

`Prog` has a similar structure to the free monad and allows expressing different
effects by instantiating `sig` with an appropriate functor. Different effects
can be combined by means of the type operator `+` and a subtyping relation.

```Haskell
data (sig1 + sig2) cnt = Inl (sig1 cnt) | Inr (sig2 cnt)
```

Combinations of effects can have different semantics, depending on the order in which
the handlers are applied. For example, the combination of nondeterminism and state
can be either *local* or *global*, that is, every branch has a copy of the state or
all branches work with the same state.
