# Coq

In addition to the concepts presented in [Effect Handlers in Scope](https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/haskell2014.pdf), this implementation is based on the ideas of [One Monad to Prove Them All](https://arxiv.org/pdf/1805.08059.pdf).

* Classes.v: Type classes required for deep sharing
* Container.v: Definition of the container class and effect containers
* DataM.v: Lifted data type definitions, lifted function definitions and type class instances
* Effect.v: Definitions of smart constructors for effect syntax
* Eq.v: Equality for the program type and equivalence relation proofs
* Example.v: Test suite
* Free.v: Definition of the free monad, a stronger induction principle, monad operations and proofs of the monad laws
* Handler.v: Handlers for non-determinism, state and sharing, as well as the program handler
* Intro.v: Examples and definitions from the Coq introduction
* Laws.v: Proofs of the Laws of Sharing
* PermSort.v: Permutation sort example algorithm
* Prog.v: Type definitions of `NDShare` and `Prog`
* Search.v: Definition of choice trees and the depth-first search algorithm
