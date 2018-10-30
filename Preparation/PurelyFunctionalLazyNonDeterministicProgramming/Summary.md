Purely Functional Lazy Non-deterministic Programming is a paper about combining
non-strict evaluation, sharing and non-determinism, embedded into existing
languages. The former enables expressing infinite data structures, sharing
increases performance by avoiding redundant computations, and the latter can be
useful in the context of testing and search.

The naive combination of all three features does not work as expected in languages
like OCaml or Haskell. For example, the definition of `sort :: MonadPlus m => [Int] -> m [Int]`
loses non-strictness when non-determinism is encoded monadically. To retain
non-strictness, data types are redefined to explicitly represent non-deterministic
components. Unfortunately, this approach sacrifices sharing because shared variables
represent non-deterministic computations instead of fully determined values.

The solution to the absence of sharing is an explicit `share :: m a -> m (m a)` operation.
By means of a few observations, the laws of sharing are established.

```
ret x >>= k = k x (Lret)
a >>= ret = a (Rret)
(a >>= k1 ) >>= k2 = a >>= λ x. k1 x >>= k2 (Bassc)
MZero >>= k = MZero (Lzero)
(a ⊕ b) >>= k = (a >>= k) ⊕ (b >>= k) (Ldistr)
share (a ⊕ b) = share a ⊕ share b (Choice)
share MZero = ret MZero (Fail)
share ⊥ = ret ⊥ (Bot)
share (ret (c x1 . . . xn )) = share x1 >>= λ y1. ... (HNF)
                               share xn >>= λ yn. ret (ret (c y1 ... yn ))
```

The laws hold only *up to observation*, that is, for some target monads, certain
aspects, like the order of choices in the set monad, are not observable.

The simple version of the implementation of `share` works by keeping evaluated in
a local store. The store can be different for non-deterministic branches and is
used query if a demanded expression has already been evaluated. If this is the
case, the cached result is returned. Otherwise, the expression is evaluated and
added to the store. To implement deep sharing, the `share` operation has to
traverse the arguments recursively and apply `share` to each of them.

When it comes to observing the results, there are two requirements that the
target monad needs to fulfill. Otherwise, the observed results might differ
from the expected results according to the `share` laws.

* Idempotence of mplus: `m ⊕ m = m` (Multiplicity of results)
* Distributivity of bind over mplus: `a >>= λx.(f x ⊕ g x) = (a >>= f) ⊕ (a >>= g)` (Order of results)

The generalized, efficient implementation is realized by adding the type classes
`NonDet` to interface non-deterministic data and `Share` to abstract types
of shared values and monads. The store is implemented by means of the state monad
transformer. The performance of the implementation can be improved by removing
superfluous pattern matching and state manipulations as well as doing some
mechanical simplifications.

