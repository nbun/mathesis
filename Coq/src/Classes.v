Require Import Thesis.Prog.

Class Shareable (A : Type) :=
  {
    shareArgs : A -> Prog A
  }.

Class Normalform (A B : Type) :=
  {
    nf : Prog A -> Prog B
  }.
