Require Import Thesis.Prog.

Class Shareable (A : Type) :=
  {
    shareArgs : A -> Prog A
  }.

Class Normalform (A B : Type) :=
  {
    nf  : Prog A -> Prog B;
    nf' : A -> Prog B;
    nf_impure: forall s (pf : _ -> Prog A),
        nf (impure (ext s pf)) = impure (ext s (fun p => nf (pf p)));
    nf_pure : forall (x : A),
        nf (pure x) = nf' x             
  }.
