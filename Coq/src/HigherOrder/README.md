# Higher-Order

Most files are structured identically to the first-order implementation.
Due to non-generalized implementation, which is necessary due to Coq's termination checks, many definitions are repeated here.
Thus, comments are omitted unless there is a relevant difference to the first-order implementation.

* Classes.v: Type classes required for deep sharing
* Container.v: Definition of the container class and effect containers
* DataM.v: Lifted data type definitions, lifted function definitions and type class instances
* Effect.v: Definitions of smart constructors for effect syntax
* Example.v: Test suite without examples that contain effectful lists
* Free.v: Definition of the free monad, a stronger induction principle, monad operations and proofs of the monad laws
* Handler.v: Handlers for non-determinism, state and sharing, as well as the program handler
* Prog.v: Type definitions of `NDShare` and `Prog`
