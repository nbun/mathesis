Require Import Thesis.Free.
Require Import Thesis.Container.
Require Import Thesis.Effect.
Require Import Thesis.Base.
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

Fixpoint runState A (n : nat) (fc : Free NDShare A) : Free (C__Comb C__Sharing C__Choice) A :=
  match fc with
  | pure x => pure x
  | impure (ext (inl (sget _))    pf) => runState n  (pf (pget n))
  | impure (ext (inl (sput s'))   pf) => runState s' (pf (pput s'))
  | impure (ext (inr (inr sfail)) _)  => Fail__SC
  | impure (ext (inr (inr (schoice mid))) pf) => Choice__SC mid (runState n (pf true)) (runState n (pf false))
  | impure (ext (inr (inl (ssharing n)))  pf) => Share'__SC n (runState n (pf (psharing n)))
  end.

Fixpoint nameChoices (A : Type) (scope next : nat) (fs : Free (C__Comb C__Sharing C__Choice) A) : Free C__Choice A  :=
  match fs with
  | pure x => pure x
  | impure (ext (inl (ssharing n)) pf) => nameChoices n 1 (pf (psharing n))
  | impure (ext (inr sfail)        pf) => Fail__C
  | impure (ext (inr (schoice _))  pf) => let l := nameChoices scope (2 * next) (pf true) in
                                         let r := nameChoices scope (2 * next + 1) (pf false)
                                         in Choice__C (Some (scope, next)) l r
  end.

Fixpoint runSharing A (fs : Free (C__Comb C__Sharing C__Choice) A) : Free C__Choice A :=
  match fs with
  | pure x => pure x
  | impure (ext (inl (ssharing n))  pf) => nameChoices n 1 (pf (psharing n))
  | impure (ext (inr sfail)         _)  => Fail__C
  | impure (ext (inr (schoice mid)) pf) => Choice__C mid (runSharing (pf true)) (runSharing (pf false))
  end.

Definition handle A (fs : Free NDShare A) : list A :=
  collectVals (runChoice (runSharing (runState 1 fs))).

Section Examples.
  Definition Coin : Free NDShare nat := Choice None (pure 0) (pure 1).
  Definition Coin__Bool : Free NDShare bool := Choice None (pure true) (pure false).

  Definition addM (fn1 fn2 : Free NDShare nat) : Free NDShare nat :=
    fn1 >>= fun n1 => fn2 >>= fun n2 => pure (n1 + n2).

  Definition orM (fn1 fn2 : Free NDShare bool) : Free NDShare bool :=
    fn1 >>= fun b => match b with
                  | true => pure true
                  | false => fn2
                  end.

  Definition duplicate A (fx : Free NDShare A) : Free NDShare (A * A) :=
    fx >>= fun x => fx >>= fun y => pure (x,y).

  Example e1 : Free NDShare (nat * nat) := Share Coin >>= fun x => duplicate x.
  
  Example e2 : Free NDShare nat := Share Coin >>= fun x => addM x x.

  Example e3 : Free NDShare bool := orM (pure true) Fail.
  Eval compute in handle e3.

End Examples.