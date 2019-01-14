Require Import Thesis.Free.
Require Import Thesis.Container.

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

Definition Fail A : Free C__Choice A :=
  impure (ext sfail (fun p : Pos__Choice sfail => match p with end)).

Arguments Fail {_}.

Definition Choice' A mid l r : Free C__Choice A :=
  impure (ext (schoice mid) (fun p : Pos__Choice (schoice mid) => if p then l else r)).


Fixpoint runState A (s : S) (fc : Free C__State A) : S * A :=
  match fc with
  | pure x => (s,x)
  | impure (ext sget      pf) => runState s  (pf (pget s))
  | impure (ext (sput s') pf) => runState s' (pf (pput s'))
  end.

Definition Get (A : Type) : Free C__State S :=
  impure (ext sget (fun p : Pos__State sget => match p with pget s => pure s end)).

Arguments Get {_}.

Definition Put (A : Type) (s : S) : Free C__State unit :=
  impure (ext (sput s) (fun p : Pos__State (sput s) => match p with pput s => pure tt end)).


Arguments Put {_} s.

Fixpoint nameChoices (A : Type) (scope next : nat) (fs : Free (C__Comb C__Sharing C__Choice) A) : Free C__Choice A  :=
  match fs with
  | pure x => pure x
  | impure (ext (inl (ssharing n)) pf) => nameChoices n 1 (pf (psharing n))
  | impure (ext (inr sfail)        pf) => Fail A
  | impure (ext (inr (schoice _))  pf) => let l := nameChoices scope (2 * next) (pf true) in
                                         let r := nameChoices scope (2 * next + 1) (pf false)
                                         in Choice' (Some (scope, next)) l r
  end.

Fixpoint runSharing A (fs : Free (C__Comb C__Sharing C__Choice) A) : Free C__Choice A :=
  match fs with
  | pure x => pure x
  | impure (ext (inl (ssharing n))  pf) => nameChoices n 1 (pf (psharing n))
  | impure (ext (inr sfail)         _)  => Fail A
  | impure (ext (inr (schoice mid)) pf) => Choice' mid (runSharing (pf true)) (runSharing (pf false))
  end.

(* Definition Share' A F C__F (n : nat) (fs : Free (C__Comb C__Sharing C__F) A) : Free (C__Comb C__Sharing C__F) A := *)
(*   impure (ext (fun p : Pos__Comb (inl (ssharing n)) => fs)). *)


(* Definition Share (M: Type -> Type) `(Monad M) A (p : M A) : M (M A) := *)
(*   Get nat nat >>= fun i => Put nat (i + 1) >>= fun _ => ret (ret p). *)
  
Definition Share A (fp : Free (C__Comb (C__Comb (C__State nat) C__Sharing) C__Choice) A) : Free (C__Comb (C__Comb (C__State nat) C__Sharing) C__Choice) (Free ((C__Comb (C__Comb (C__State nat) C__Sharing) C__Choice)) A) :=
  Get nat nat >>= fun i => Put nat (i + 1) >>= fun _ => ret fp.

  