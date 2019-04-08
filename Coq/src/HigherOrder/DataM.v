(** Lifted data type definitions, lifted function definitions and type class instances *)
Require Import Thesis.HigherOrder.Prog.
Require Import Thesis.HigherOrder.Effect.
Require Import Thesis.HigherOrder.Classes.
Require Import Thesis.HigherOrder.Handler.

Set Implicit Arguments.

Section Prim.
  Definition Coin : Prog nat := Choice None (pure 0) (pure 1).
  Definition Coin__Bool : Prog bool := Choice None (pure true) (pure false).
  
  Definition addM (fn1 fn2 : Prog nat) : Prog nat :=
    fn1 >>= fun n1 => fn2 >>= fun n2 => pure (n1 + n2).
  
  Definition orM (fn1 fn2 : Prog bool) : Prog bool :=
    fn1 >>= fun b => match b with
                  | true => pure true
                  | false => fn2
                  end.
  
  Definition notM (fn : Prog bool) : Prog bool :=
    fn >>= fun b => pure (negb b).
 
  Definition duplicate A (fx : Prog A) : Prog (A * A) :=
    fx >>= fun x => fx >>= fun y => pure (x,y).

  Global Instance shareable__Nat : Shareable nat :=
    {
      shareArgs := pure
    }.
  
  Global Instance shareable__Bool : Shareable bool :=
    {
      shareArgs := pure
    }.

  Definition nf__nat (n : Prog nat) :=
    free_bind n (fun n' => pure n').

  Lemma nf_impure__nat : forall s (pf : _ -> Prog nat) pfx,
      nf__nat (impure (ext s pf pfx)) = impure (ext s (fun p => nf__nat (pf p)) pfx).
  Proof. trivial. Qed.

  Global Instance normalform__nat : Normalform nat nat :=
    {
      nf := nf__nat;
      nf_impure := nf_impure__nat
    }.
  
  Definition nf__bool (b : Prog bool) :=
    b >>= fun b' => pure b'.

  Lemma nf_impure__bool : forall s (pf : _ -> Prog bool) pfx,
      nf__bool (impure (ext s pf pfx)) = impure (ext s (fun p => nf__bool (pf p)) pfx).
  Proof. trivial. Qed.

  Global Instance normalform__bool : Normalform bool bool :=
    {
      nf := nf__bool;
      nf_impure := nf_impure__bool
    }.
End Prim.

Section Pair.
  Inductive Pair A B :=
  | Pair' : Prog A -> Prog B -> Pair A B.
  
  Definition pairM A B (fst : Prog A) (snd : Prog B) : Prog (Pair A B) :=
    pure (Pair' fst snd).

  Definition firstM A B (fp : Prog (Pair A B)) : Prog A :=
    fp >>= fun '(Pair' fst _) => fst.

  Definition secondM A B (fp : Prog (Pair A B)) : Prog B :=
    fp >>= fun '(Pair' _ snd) => snd.

  Definition dup' (fp : Prog (Pair bool bool)) : Prog (Pair bool bool) :=
    pairM (firstM fp) (firstM fp).

  Definition dup A (fx : Prog A) : Prog (Pair A A) :=
    pairM fx fx.

  Definition dupShare A `{Shareable A} (fx : Prog A) : Prog (Pair A A) :=
    Share fx >>= fun x => pairM x x.

  Definition shareArgs__Pair A B `(Shareable A) `(Shareable B) (p : Pair A B) : Prog (Pair A B) :=
    match p with
    | Pair' a b => Share a >>= fun sa => Share b >>= fun sb => pairM sa sb
    end.

  Global Instance shareable__Pair A B `(sa : Shareable A) `(sb : Shareable B) : Shareable (Pair A B) :=
    {
      shareArgs := @shareArgs__Pair A B sa sb
    }.

  Definition nf__Pair A B C D `{Normalform A C} `{Normalform B D} (stp : Prog (Pair A B)) : Prog (Pair C D) :=
    stp >>= fun '(Pair' sp1 sp2) =>
              nf sp1 >>= fun b1 =>
              nf sp2 >>= fun b2 =>
              pairM (pure b1) (pure b2).

  Lemma nf_impure__Pair A B C D nf__AC nf__BD : forall s (pf : _ -> Prog (Pair A B)) pfx,
      @nf__Pair A B C D nf__AC nf__BD (impure (ext s pf pfx)) = impure (ext s (fun p => nf__Pair (pf p)) pfx).
  Proof. trivial. Qed.

  Global Instance normalform__Pair A B C D {nf__AC : Normalform A C} {nf__BD : Normalform B D} : Normalform (Pair A B) (Pair C D) :=
    {
      nf := fun x => nf__Pair x;
      nf_impure := nf_impure__Pair nf__AC nf__BD
    }.

End Pair.

(** Failed definition of the lifted list type *)
Section List.

  (** Fails due to non-strictly positive occurrence of Free in Cons' *)
  Fail Inductive List A :=
  | Nil'  : List A
  | Cons' : Prog A -> Prog (List A) -> List A. 

  (** CPS defintion of List *)
  Inductive List A :=
  | Nil' : List A
  | Cons' {T : Type} : Prog A -> Prog T -> (T -> List A) -> List A.

  (** Using CPS-style lists leads to universe inconsistency and other type-hierarchy related errors *)
  Fail Definition consM A (fx : Prog A) (fxs : Prog (List A)) : Prog (List A) :=
    pure (@Cons' A (List A) fx fxs id).
End List.