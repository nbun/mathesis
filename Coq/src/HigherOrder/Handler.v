Require Import Thesis.HigherOrder.Base.
Require Import Thesis.HigherOrder.Classes.
Require Import Thesis.HigherOrder.Effect.
Require Import Thesis.HigherOrder.Prog.
Require Import Thesis.Search.

Set Implicit Arguments.

Definition run A (fz : Free C__Zero A) : A :=
  match fz with
  | pure x => x
  | impure e => match e with
                 ext s _ _ => match s with end
               end
  end.

Fixpoint runChoice A (fc : Free C__Choice A) : Tree A :=
  match fc with
  | pure x => Leaf x
  | impure (ext sfail   _ _)  => Empty A
  | impure (ext (schoice mid) pf _) => Branch mid (runChoice (pf true)) (runChoice (pf false))
  end.

Fixpoint runState A (n : nat * nat) (fc : Prog A) : Prog__SC A :=
  match fc with
  | pure x => pure x
  | impure (ext (inl (sget _))    pf _) => runState n  (pf (pget n))
  | impure (ext (inl (sput s'))   pf _) => runState s' (pf (pput s'))
  | impure (ext (inr (inr sfail)) _ _)  => Fail__SC
  | impure (ext (inr (inr (schoice mid))) pf _) => Choice__SC mid (runState n (pf true)) (runState n (pf false))
  | impure (ext (inr (inl (ssharing m T) as s))  pf pfx) =>
    let s : @Shape _ NDShare__SC := inl (ssharing m T)
    in impure (ext s (fun p : @Pos _ NDShare__SC s => runState n (pf p))
                   (fun p : @PosX _ NDShare__SC s => runState n (pfx p)))
  end.

Definition tripl A B C (p : A * B) (c : C) : A * B * C :=
  let '(a,b) := p in (a,b,c).

Fixpoint nameChoices  A (next : nat) (scope : nat * nat) (fs : Prog__SC A)
  : Free C__Choice A :=
   match fs with
  | pure x => pure x
  | impure (ext (inl (ssharing m X)) pf pfx) =>
    let s : @Shape _ C__Sharing := ssharing m X
    in nameChoices 1 m (pfx (pshared s)) >>=
                   fun x => nameChoices next scope (pf (pcont s x))
  | impure (ext (inr sfail)        pf _) => Fail__C
  | impure (ext (inr (schoice _))  pf _) =>
    let l := nameChoices (next + 1) scope (pf true) in
    let r := nameChoices (next + 1) scope (pf false)
    in Choice__C (Some (tripl scope next)) l r
  end.
    
Fixpoint runSharing A (fs : Free (C__Comb C__Sharing C__Choice) A) : Free C__Choice A :=
  match fs with
  | pure x => pure x
  | impure (ext (inl (ssharing n X))  pf pfx) =>
    let s : @Shape _ C__Sharing := ssharing n X
    in nameChoices 1 n (pfx (pshared s)) >>=
                   fun x => runSharing (pf (pcont s x))
  | impure (ext (inr sfail)         _ _)  => Fail__C
  | impure (ext (inr (schoice mid)) pf _) =>
    Choice__C mid (runSharing (pf true)) (runSharing (pf false))
  end.

Definition handle A `{Normalform A A} (fs : Prog A) : list A :=
  collectVals (runChoice (runSharing (runState (0,0) (nf fs)))).
