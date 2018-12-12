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

Handlers can also be non-orthogonal, that is, effects influence each other. One example
is `Cutfail`, an effect that can prevent the evaluation of unexplored branches. The
scope of the effect is limited by the function `call`, where the interplay of the effects
can be observed.

```Haskell
call :: (Nondet <: sig) ⇒ Prog (Cut + sig) a → Prog sig a
call p = go p fail where
  go :: (Nondet <: sig) ⇒ Prog (Cut + sig) a → Prog sig a → Prog sig a
  go (Return a) q = return a q
  go (Fail)     q = q
  go (Cutfail)  q = fail
  go (p1 :8 p2 ) q = go p1 (go p2 q)
  go (Other op) q = Op (fmap (flip go q) op)
```

Functions like `call` are called scoping handlers because they limit the scope of effect.
Since such handlers unite semantics and scoping, unforeseen side effects can occur. As
shown in the grammar example, the necessary scoping might conflict with the desired
semantics. One solution is to introduce explicit scoping by means of `begin` and `end`
expressions.

```Haskell
data Call cnt = BCall0 cnt | ECall0 cnt
pattern BCall p ← (project → Just (BCall0 p))
pattern ECall p ← (project → Just (ECall0 p))
```

The adapted `call` function respects these markers. While this solution has some (amendable)
flaws in regard to local and global semantics, another approach is also presented.

```Haskell
data Prog sig a = Return a 
                | Op (sig (Prog sig) a)
```

Higher-Order programs allows modeling scoping in higher-order syntax. With the adapted
signature `sig :: (∗ → ∗) → ∗ → ∗ i` and a new version of `fmap`, namely `emap`, the
monad instance looks very similar to the original one. Existing signatures can be lifted
but handlers need to be adapted. While this makes the individual effect handlers slightly
more complicated, the result is more expressive and a more natural way to denote scoping.
