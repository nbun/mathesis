Require Import Thesis.Free.
Require Import Thesis.Container.
Require Import Thesis.Effect.
Require Import Thesis.Base.

Set Implicit Arguments.

Definition run A (fz : Free C__Zero A) : A :=
  match fz with
  | pure x => x
  | impure e => match e with
                 ext s _ => match s with end
               end
  end.

Fixpoint runChoice A (fc : Free C__Choice A) : list A :=
  match fc with
  | pure x => cons x nil
  | impure (ext sfail   _)  => nil
  | impure (ext (schoice mid) pf) => app (runChoice (pf true)) (runChoice (pf false))
  end.

Fixpoint runState A (n : nat) (fc : Free NDShare A) : Free (C__Comb C__Sharing C__Choice) A :=
  match fc with
  | pure x => pure x
  | impure (ext (inl (sget _))    pf) => runState n  (pf (pget n))
  | impure (ext (inl (sput s'))   pf) => runState s' (pf (pput s'))
  | impure (ext (inr (inr sfail)) _)  => Fail__SharingChoice
  | impure (ext (inr (inr (schoice mid))) pf) => Choice__SharingChoice mid (runState n (pf true)) (runState n (pf false))
  | impure (ext (inr (inl (ssharing n)))  pf) => Share'__SharingChoice n (runState n (pf (psharing n)))
  end.

Fixpoint nameChoices (A : Type) (scope next : nat) (fs : Free (C__Comb C__Sharing C__Choice) A) : Free C__Choice A  :=
  match fs with
  | pure x => pure x
  | impure (ext (inl (ssharing n)) pf) => nameChoices n 1 (pf (psharing n))
  | impure (ext (inr sfail)        pf) => Fail__Choice
  | impure (ext (inr (schoice _))  pf) => let l := nameChoices scope (2 * next) (pf true) in
                                         let r := nameChoices scope (2 * next + 1) (pf false)
                                         in Choice__Choice (Some (scope, next)) l r
  end.

Fixpoint runSharing A (fs : Free (C__Comb C__Sharing C__Choice) A) : Free C__Choice A :=
  match fs with
  | pure x => pure x
  | impure (ext (inl (ssharing n))  pf) => nameChoices n 1 (pf (psharing n))
  | impure (ext (inr sfail)         _)  => Fail__Choice
  | impure (ext (inr (schoice mid)) pf) => Choice__Choice mid (runSharing (pf true)) (runSharing (pf false))
  end.

Section Examples.
  Definition p1 : Free NDShare nat := Choice None (ret 42) (ret 43).
  Eval compute in runChoice (runSharing (runState 1 p1)).

End Examples.