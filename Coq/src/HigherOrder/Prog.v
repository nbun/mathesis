(** Type definitions for NDShare and Prog *)
Require Import Thesis.HigherOrder.Free.
Require Import Thesis.HigherOrder.Container.

Export Thesis.HigherOrder.Free.
Export Thesis.HigherOrder.Container.

Definition NDShare := C__Comb (C__State (nat * nat)) (C__Comb C__Sharing C__Choice).

Definition NDShare__SC := C__Comb C__Sharing C__Choice.

Definition Prog := Free NDShare.

Definition Prog__SC := Free NDShare__SC.
