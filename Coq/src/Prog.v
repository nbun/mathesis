(** Type definitions of NDShare and Prog *)
Require Import Thesis.Free.
Require Import Thesis.Container.

(** Free and Container are re-exported since they are required in order
    to use the type synonyms *)
Export Thesis.Free.
Export Thesis.Container.

(** Combination container of the effect stack *)
Definition NDShare := C__Comb (C__State (nat * nat)) (C__Comb C__Sharing C__Choice).

Definition NDShare__SC := C__Comb C__Sharing C__Choice.

(** Equivalent to the Haskell NDShare type *)
Definition Prog := Free NDShare.

Definition Prog__SC := Free NDShare__SC.
