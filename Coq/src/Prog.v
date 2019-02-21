Require Import Thesis.Free.
Require Import Thesis.Container.

Export Thesis.Free.
Export Thesis.Container.

Definition NDShare := C__Comb (C__State (nat * nat)) (C__Comb C__Sharing C__Choice).

Definition NDShare__SC := C__Comb C__Sharing C__Choice.

Definition Prog := Free NDShare.

Definition Prog__SC := Free NDShare__SC.
