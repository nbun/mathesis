Require Import Thesis.Container.
Require Import Thesis.Free.
Require Import Thesis.Base.

Set Implicit Arguments.

Definition NDShare := C__Comb (C__State nat) (C__Comb C__Sharing C__Choice).

Definition NDShareF := Comb (State nat) (Comb Sharing Choice).

Definition Pos__NDShare := @Pos__Comb (State nat) (Comb Sharing Choice) (C__State nat) (C__Comb C__Sharing C__Choice).

Definition effect (A : Type) := @impure NDShareF NDShare A.

Definition Fail A : Free NDShare A :=
  let s := inr (inr sfail)
  in effect (ext s (fun p : Pos__NDShare s => match p with end)).

Definition Fail__Choice A : Free C__Choice A :=
  let s := sfail
  in @impure Choice C__Choice A (ext s (fun p : Pos__Choice s => match p with end)).

Arguments Fail {_}.
Arguments Fail__Choice {_}.

Definition Choice__Choice A mid l r : Free C__Choice A :=
  let s := schoice mid
  in @impure Choice C__Choice A (ext s (fun p : Pos__Choice s => if p then l else r)).

Definition Choice A mid l r : Free NDShare A :=
  let s := inr (inr (schoice mid))
  in effect (ext s (fun p : Pos__NDShare s => if p then l else r)).

Definition Get : Free NDShare nat :=
  let s := inl (sget nat)
  in effect (ext s (fun p : Pos__NDShare s => match p with pget s => pure s end)).

Definition Put (n : nat) : Free NDShare unit :=
  let s := inl (sput n)
  in effect (ext s (fun p : Pos__NDShare s => match p with pput s => pure tt end)).

Definition Share' (n : nat) A (fs : Free NDShare A) : Free NDShare A :=
  let s := inr (inl (ssharing n))
  in effect (ext s (fun p : Pos__NDShare s => fs)).

Definition Share A `(Monad (Free NDShare)) (fp : Free NDShare A) : Free NDShare (Free NDShare A) :=
  Get >>= fun i => Put (i * 2) >>= fun _=> ret (Share' i (Put (i * 2 + 1) >>= fun _ => ret fp)).