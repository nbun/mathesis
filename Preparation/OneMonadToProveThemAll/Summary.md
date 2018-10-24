One Monad to Prove Them all is a paper about proving properties of other languages in Coq.
Transferring partial functions to Coq is problematic because Coq requires all functions to
be provably total. Nevertheless, partial functions are an important part of languages like
Haskell and a solution that can model partiality is desired.

One approach is to model Haskell programs monadically in Coq. This approach comes with a
challenge: Constructor arguments may only occur 'strictly positive' in Coq, meaning that
the defined type only occurs on the left side of a function arrow. The reason for this
restriction is that general recursion would otherwise be available, for example, as
evidenced by the type *Mu*. This would break Coq's logic.

```Coq
Fail Inductive Mu A := mu : (Mu A → A) → Mu A.
```

The free monad could help circumventing the problem by replacing the monadic part. As it
turns out, `Free` suffers the same problem of strict positivity in Coq. Due its versatility
in representing other monads when instantiated with an appropriate functor, another way
of representing `Free` is needed.

```Coq
Fail Inductive Free F A :=
| pure : A → Free F A
| impure : F (Free F A) → Free F A.

```

A container is an abstraction of data types that store values. It consists of two types
where one represents all possible shapes and the other maps shapes to positions. An
extension of a container adds a function that maps valid positions to values.

```Coq
Inductive Ext Shape (Pos : Shape → Type) A := ext : ∀ s, (Pos s → A) → Ext Shape Pos A.
```

With the power of containers abstracted into a type class, the definition of `Free` is finally
accepted by Coq with `F` as a type constructor.

```Coq
Inductive Free (CF : Container F) A :=
| pure : A → Free CF A
| impure : Ext Shape Pos (Free CF A) → Free CF A.
```

Based on the new definition of `Free`, functions that map instances of `Free` to the corresponding
monad can be defined. The other way around, however, does not always work, for example, in case of
the list monad. As a consequence, structural equality does not work in these cases and a custom
equality operator is necessary. The operator works by mapping instances of the free monad to their
original monad representations, which allows using the structural equality on the resulting monadic
terms again. While the current approach allows modeling many monads, functional types cannot be 
represented yet.

Proving properties about Haskell code that has been transformed requires explicitly stating an induction
principle due to the definition of `Free`. Proofs for the `Identity` and `Maybe` monad work similar
using the induction principle. Even better, proofs about any monad that can be represented by a
container-based instance of the free monad hold regardless of the specific instance.

The approach presented in the paper could be extended to other languages, for example Curry, that feature
additional effects like non-determinism. 
