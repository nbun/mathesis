Require Import Thesis.HigherOrder.Base.
Require Import Thesis.HigherOrder.Prog.
Require Import Thesis.HigherOrder.Classes.

Set Implicit Arguments.

Definition Get : Prog (nat * nat) :=
  let s : @Shape _ NDShare := inl (sget (nat * nat))
  in impure (ext s (fun p : @Pos _ NDShare s => match p with pget s => pure s end)
                 (fun p : @PosX _ NDShare s => match p with end)).

Definition Put (n : nat * nat) : Prog unit :=
  let s : @Shape _ NDShare := inl (sput n)
  in impure (ext s (fun p : @Pos _ NDShare s => match p with pput s => pure tt end)
                 (fun p : @PosX _ NDShare s => match p with end)).

Definition Share' (n : nat * nat) A (fs : Prog A) : Prog A :=
  let s : @Shape _ NDShare := inr (inl (ssharing n A))
  in impure (ext s (fun p : @Pos _ NDShare s => pure p)
                 (fun p : @PosX _ NDShare s => fs)).

Definition Share'__SC (n : nat * nat) A (fs : Prog__SC A) : Prog__SC A :=
  let s : @Shape _ NDShare__SC := (inl (ssharing n A))
  in impure (ext s (fun p : @Pos _ NDShare__SC s => pure p)
                 (fun p : @PosX _ NDShare__SC s => fs)).

Definition Share A `(Shareable A) (p : Prog A) : Prog (Prog A) :=
  Get >>= fun '(i,j) =>
  Put (i + 1, j) >>
  pure (Share' (i,j)
               (Put (i, j + 1) >>
                p >>= fun x =>
                Put (i + 1, j) >>
                shareArgs x >>= fun x' =>
                Put (i + 1, j) >>
                pure x')).

Arguments Share {_} {_} p.

Definition Fail A : Prog A :=
  let s : @Shape _ NDShare := inr (inr sfail)
  in impure (ext s (fun p : @Pos _ NDShare s => match p with end)
                 (fun p : @PosX _ NDShare s => match p with end)).

Arguments Fail {_}.

Definition Fail__C A : Free C__Choice A :=
  let s : @Shape _ C__Choice := sfail
  in impure (ext s (fun p : Pos__Choice s => match p with end)
                 (fun p : PosX__Choice s => match p with end)).

Arguments Fail__C {_}.

Definition Fail__SC A : Free (C__Comb C__Sharing C__Choice) A :=
  let s : @Shape _ NDShare__SC := inr sfail
  in impure (ext s (fun p : @Pos _ NDShare__SC s => match p with end)
                 (fun p : @PosX _ NDShare__SC s => match p with end)).

Arguments Fail__SC {_}.

Definition Choice__C A mid l r : Free C__Choice A :=
  let s : @Shape _ C__Choice := schoice mid
  in impure (ext s (fun p : Pos__Choice s => if p then l else r)
                 (fun p : PosX__Choice s => match p with end)).

Definition Choice__SC A mid l r : Prog__SC A :=
  let s : @Shape _ NDShare__SC := inr (schoice mid)
  in impure (ext s (fun p : @Pos _ NDShare__SC s => if p then l else r)
                 (fun p : @PosX _ NDShare__SC s => match p with end)).

Definition Choice A mid l r : Prog A :=
  let s : @Shape _ NDShare := inr (inr (schoice mid))
  in impure (ext s (fun p : @Pos _ NDShare s => if p then l else r)
                 (fun p : @PosX _ NDShare s => match p with end)).

Notation "x ? y" := (Choice None x y) (at level 80).
