Require Import Thesis.Base.
Require Import Thesis.Classes.
Require Import Thesis.Effect.
Require Import Thesis.Prog.
Require Import Thesis.Search.

Set Implicit Arguments.

Definition run A (fz : Free C__Zero A) : A :=
  match fz with
  | pure x => x
  | impure e => match e with
                 ext s _ => match s with end
               end
  end.

Fixpoint runChoice A (fc : Free C__Choice A) : Tree A :=
  match fc with
  | pure x => Leaf x
  | impure (ext sfail   _)  => Empty A
  | impure (ext (schoice mid) pf) => Branch mid (runChoice (pf true)) (runChoice (pf false))
  end.

Fixpoint runState A (n : nat * nat) (fc : Prog A) : Free (C__Comb C__Sharing C__Choice) A :=
  match fc with
  | pure x => pure x
  | impure (ext (inl sget)      pf) => runState n (pf n)
  | impure (ext (inl (sput s')) pf) => runState s' (pf tt)
  | impure (ext (inr s) pf)         => impure (cmap (runState n) (ext s pf))
  end.

Definition tripl A B C (p : A * B) (c : C) : A * B * C :=
  let '(a,b) := p in (a,b,c).

Fixpoint runSharing A (fs : Free (C__Comb C__Sharing C__Choice) A) : Free C__Choice A :=
  let fix nameChoices (next : nat) (scope : nat * nat) (scopes : list (nat * nat)) (fs : Prog__SC A)
  : Free C__Choice A  :=
      match fs with
      | pure x => pure x
      | impure (ext (inl (sbsharing n)) pf) =>
        nameChoices 1 n (cons n scopes) (pf tt)
      | impure (ext (inl (sesharing n)) pf) =>
        match scopes with
        | cons _ (cons j js) as ks => nameChoices next j ks (pf tt) 
        | _                        => runSharing (pf tt)
        end
      | impure (ext (inr sfail)        pf) => Fail__C
      | impure (ext (inr (schoice _))  pf) =>
        let l := nameChoices (next + 1) scope scopes (pf true) in
        let r := nameChoices (next + 1) scope scopes (pf false)
        in Choice__C (Some (tripl scope next)) l r
      end
  in match fs with
     | pure x => pure x
     | impure (ext (inl (sbsharing n))  pf) =>
       nameChoices 1 n (cons n nil) (pf tt)
     | impure (ext (inl (sesharing n))  pf) => runSharing (pf tt)
     | impure (ext (inr s) pf) => impure (cmap (@runSharing A) (ext s pf))
     end.

Definition handle A `{Normalform A A} (fs : Prog A) : list A :=
  collectVals (runChoice (runSharing (runState (0,0) (nf fs)))).
