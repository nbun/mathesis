Require Import Thesis.Base.
Require Import Thesis.Prog.
Require Import Thesis.Classes.

Set Implicit Arguments.

Definition Get : Prog nat :=
  let s : @Shape _ NDShare := inl (sget nat)
  in impure (ext s (fun p : @Pos _ NDShare s => match p with pget s => pure s end)).

Definition Put (n : nat) : Prog unit :=
  let s : @Shape _ NDShare := inl (sput n)
  in impure (ext s (fun p : @Pos _ NDShare s => match p with pput s => pure tt end)).

Definition BeginShare (n : nat) : Prog unit :=
  let s : @Shape _ NDShare := inr (inl (sbsharing n))
  in impure (ext s (fun p : @Pos _ NDShare s => pure tt)).

Definition EndShare (n : nat) : Prog unit :=
  let s : @Shape _ NDShare := inr (inl (sesharing n))
  in impure (ext s (fun p : @Pos _ NDShare s => pure tt)).

Definition BeginShare__SC A (n : nat) (fp : Prog__SC A) : Prog__SC A :=
  let s : @Shape _ NDShare__SC := inl (sbsharing n)
  in impure (ext s (fun p : @Pos _ NDShare__SC s => fp)).

Definition EndShare__SC A (n : nat) (fp : Prog__SC A) : Prog__SC A :=
  let s : @Shape _ NDShare__SC := inl (sesharing n)
  in impure (ext s (fun p : @Pos _ NDShare__SC s => fp)).

Definition Share A `(Shareable A) (fp : Prog A) : Prog (Prog A) :=
  Get >>= fun i =>
  Put (i * 2) >>= fun _ =>
  pure (BeginShare i >>= fun _ =>
        Put (i * 2 + 1) >>= fun _ =>
        fp >>= fun x =>
        shareArgs x >>= fun x' =>
        EndShare i >>= fun _ =>
        pure x').
Arguments Share {_} {_} fp.

Definition Fail A : Prog A :=
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

Definition Choice__C A mid l r : Free C__Choice A :=
  let s : @Shape _ C__Choice := schoice mid
  in impure (ext s (fun p : Pos__Choice s => if p then l else r)).

Definition Choice__SC A mid l r : Prog__SC A :=
  let s : @Shape _ NDShare__SC := inr (schoice mid)
  in impure (ext s (fun p : @Pos _ NDShare__SC s => if p then l else r)).

Definition Choice A mid l r : Prog A :=
  let s : @Shape _ NDShare := inr (inr (schoice mid))
  in impure (ext s (fun p : @Pos _ NDShare s => if p then l else r)).

Notation "x ? y" := (Choice None x y) (at level 80).
