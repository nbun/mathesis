(** Type classes required for deep sharing *)
Require Import Thesis.Prog.


(** Sharing of data types with effectful components.
    The instance needs to satisfy the HNF law of sharing. *)
Class Shareable (A : Type) :=
  {
    shareArgs : A -> Prog A
  }.

(** Normalization of data types with effectful components.
    Moves effects from components to the root of the expression. *)
Class Normalform (A B : Type) :=
  {
    (** The function is split into two parts due to termination check errors
        for recrusive data types. *)
    nf  : Prog A -> Prog B;
    nf' : A -> Prog B;
    (** Property for moving nf into position functions *)
    nf_impure: forall s (pf : _ -> Prog A),
        nf (impure (ext s pf)) = impure (ext s (fun p => nf (pf p)));
    (** Property for unfolding nf on pure values *)
    nf_pure : forall (x : A),
        nf (pure x) = nf' x             
  }.
