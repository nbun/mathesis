(** Definitions of smart constuctors for effect syntax.
    If necessary, the constructors are defined for multiple
    program types from the effect stack. *)
Require Import Thesis.Prog.
Require Import Thesis.Classes.

Set Implicit Arguments.

(** Smart constructors for state effect *)
Definition Get : Prog (nat * nat) :=
  let s : @Shape _ NDShare := inl sget
  in impure (ext s pure).

Definition Put (n : nat * nat) : Prog unit :=
  let s : @Shape _ NDShare := inl (sput n)
  in impure (ext s (fun _ => pure tt)).

(** Smart constructors for sharing effect *)
Definition BeginShare (n : nat * nat) : Prog unit :=
  let s : @Shape _ NDShare := inr (inl (sbsharing n))
  in impure (ext s (fun _ => pure tt)).

Definition EndShare (n : nat * nat) : Prog unit :=
  let s : @Shape _ NDShare := inr (inl (sesharing n))
  in impure (ext s (fun _ => pure tt)).

Definition Share A `(Shareable A) (p : Prog A) : Prog (Prog A) :=
  Get >>= fun '(i,j) =>
  Put (i + 1, j) >>
  pure (BeginShare (i,j) >>
        Put (i, j + 1) >>
        p >>= fun x =>
        shareArgs x >>= fun x' =>
        Put (i + 1, j) >>
        EndShare (i,j) >>
        pure x').
Arguments Share {_} {_} p.

(** Smart constructors for non-determinism effect *)
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

(** Curry notation for the choice operator *)
Notation "x ? y" := (Choice None x y) (at level 80).
