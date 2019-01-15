Require Import Thesis.Container.
Require Import Thesis.Free.
Require Import Thesis.Base.

Set Implicit Arguments.

Definition NDShare := C__Comb (C__State nat) (C__Comb C__Sharing C__Choice).

Definition NDShare__SC := C__Comb C__Sharing C__Choice.

Definition Fail A : Free NDShare A :=
  let s : @Shape _ NDShare := inr (inr sfail)
  in impure (ext s (fun p : @Pos _ NDShare s => match p with end)).

Arguments Fail {_}.

Definition Fail__C A : Free C__Choice A :=
  let s : @Shape _ C__Choice := sfail
  in impure (ext s (fun p : Pos__Choice s => match p with end)).

Arguments Fail__C {_}.

Definition Fail__SC A : Free (C__Comb C__Sharing C__Choice) A :=
  let s : @Shape _ NDShare__SC := inr sfail
  in impure (ext s (fun p : @Pos _ NDShare__SC s => match p with end)).

Arguments Fail__SC {_}.

Definition Get : Free NDShare nat :=
  let s : @Shape _ NDShare := inl (sget nat)
  in impure (ext s (fun p : @Pos _ NDShare s => match p with pget s => pure s end)).

Definition Put (n : nat) : Free NDShare unit :=
  let s : @Shape _ NDShare := inl (sput n)
  in impure (ext s (fun p : @Pos _ NDShare s => match p with pput s => pure tt end)).

Definition Share' (n : nat) A (fs : Free NDShare A) : Free NDShare A :=
  let s : @Shape _ NDShare := inr (inl (ssharing n))
  in impure (ext s (fun p : @Pos _ NDShare s => fs)).

Definition Share'__SC (n : nat) A (fs : Free NDShare__SC A) : Free NDShare__SC A :=
  let s : @Shape _ NDShare__SC := inl (ssharing n)
  in impure (ext s (fun p : @Pos _ NDShare__SC s => fs)).

Definition Share A `(Monad (Free NDShare)) (fp : Free NDShare A) : Free NDShare (Free NDShare A) :=
  Get >>= fun i => Put (i * 2) >>= fun _=> ret (Share' i (Put (i * 2 + 1) >>= fun _ => ret fp)).

Definition Choice__C A mid l r : Free C__Choice A :=
  let s : @Shape _ C__Choice := schoice mid
  in impure (ext s (fun p : Pos__Choice s => if p then l else r)).

Definition Choice__SC A mid l r : Free NDShare__SC A :=
  let s : @Shape _ NDShare__SC := inr (schoice mid)
  in impure (ext s (fun p : @Pos _ NDShare__SC s => if p then l else r)).

Definition Choice A mid l r : Free NDShare A :=
  let s : @Shape _ NDShare := inr (inr (schoice mid))
  in impure (ext s (fun p : @Pos _ NDShare s => if p then l else r)).
