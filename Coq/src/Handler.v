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

Fixpoint runState A (n : nat) (fc : Prog A) : Free (C__Comb C__Sharing C__Choice) A :=
  match fc with
  | pure x => pure x
  | impure (ext (inl (sget _))    pf) => runState n  (pf (pget n))
  | impure (ext (inl (sput s'))   pf) => runState s' (pf (pput s'))
  | impure (ext (inr (inr sfail)) _)  => Fail__SC
  | impure (ext (inr (inr (schoice mid))) pf) => Choice__SC mid (runState n (pf true)) (runState n (pf false))
  | impure (ext (inr (inl (sbsharing m)))  pf) => BeginShare__SC m (runState n (pf (pbsharing m)))
  | impure (ext (inr (inl (sesharing m)))  pf) => EndShare__SC   m (runState n (pf (pesharing m)))
  end.

Fixpoint runSharing A (fs : Free (C__Comb C__Sharing C__Choice) A) : Free C__Choice A :=
  let fix nameChoices (next scope : nat) (scopes : list nat) (fs : Prog__SC A)
  : Free C__Choice A  :=
      match fs with
      | pure x => pure x
      | impure (ext (inl (sbsharing n)) pf) =>
        nameChoices 1 n (cons n scopes) (pf (pbsharing n))
      | impure (ext (inl (sesharing n)) pf) =>
        match scopes with
        | cons _ (cons j js) as ks => nameChoices next j ks (pf (pesharing n)) 
        | _                        => runSharing (pf (pesharing n))
        end
      | impure (ext (inr sfail)        pf) => Fail__C
      | impure (ext (inr (schoice _))  pf) =>
        let l := nameChoices (next + 1) scope scopes (pf true) in
        let r := nameChoices (next + 1) scope scopes (pf false)
        in Choice__C (Some (scope, next)) l r
      end
  in match fs with
     | pure x => pure x
     | impure (ext (inl (sbsharing n))  pf) =>
       nameChoices 1 n (cons n nil) (pf (pbsharing n))
     | impure (ext (inl (sesharing n))  pf) => runSharing (pf (pesharing n))
     | impure (ext (inr sfail)         _)  => Fail__C
     | impure (ext (inr (schoice mid)) pf) =>
       Choice__C mid (runSharing (pf true)) (runSharing (pf false))
     end.

Definition handle A `{Normalform A A} (fs : Prog A) : list A :=
  collectVals (runChoice (runSharing (runState 1 (nf fs)))).
