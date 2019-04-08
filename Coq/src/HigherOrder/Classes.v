(** Type classes required for deep sharing *)
Require Import Thesis.HigherOrder.Prog.

Class Shareable (A : Type) :=
  {
    shareArgs : A -> Prog A
  }.

Class Normalform (A B : Type) :=
  {
    nf : Prog A -> Prog B;
    nf_impure: forall s (pf : _ -> Prog A) pfx,
        nf (impure (ext s pf pfx)) = impure (ext s (fun p => nf (pf p)) pfx)

  }.
