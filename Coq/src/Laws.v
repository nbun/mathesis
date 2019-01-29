Require Import Thesis.Effect.
Require Import Thesis.Classes.
Require Import Thesis.DataM.
Require Import Thesis.Handler.
Require Import Thesis.Prog.
Require Import Thesis.Base.
Require Import Thesis.Eq.

Require Import Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

Axiom Free_Share_dec :
  forall (A : Type) (p : Prog A),
    { exists x, p = pure x } +
    { p = Fail } +
    { exists p1 p2, p = (p1 ? p2)}.

Section Free_Share_Ind.
  Variable A : Type.
  Variable P : Prog A -> Prop.

  Hypothesis HPure : forall (x : A), P (pure x).
  Hypothesis HFail : P Fail.
  Hypothesis HChoice : forall (p1 p2 : Prog A), P p1 -> P p2 -> P (p1 ? p2).

  Lemma Free_Share_Ind : forall (p : Prog A), P p.
  Proof.
    intros p.
    induction p using Free_Ind; eauto.
    destruct (Free_Share_dec (impure (ext s pf))) as [H1 | Hchoice].
    - destruct H1 as [Hpure | Hfail].
      + destruct Hpure as [x Hx]; discriminate Hx.
      + rewrite Hfail; eauto.
    - destruct Hchoice as [p1 [p2 H12]]; rewrite H12.
      dependent destruction H12.
      apply HChoice.
      + apply (H true).
      + apply (H false).
  Defined.
End Free_Share_Ind.

Section SharingLaws.
  Variable (A : Type).
  Variable nf__A : Normalform A A.

  Theorem Lret : forall f (x : A), Eq_Prog eq (pure x >>= f) (f x).
  Proof. reflexivity. Qed.
  
  Theorem Rret : forall (p : Prog A), Eq_Prog eq (p >>= pure) p.
  Proof.
    intros p.
    rewrite bind_pure.
    reflexivity.
  Qed.

  Theorem Bassc : forall (p : Prog A) (f g : A -> Prog A), Eq_Prog eq ((p >>= f) >>= g) (p >>= fun x => f x >>= g).
  Proof.
    intros p f g.
    rewrite free_bind_assoc.
    reflexivity.
  Qed.

  Theorem Lzero' : forall (f : A -> Prog A), (Fail >>= f) = Fail.
    intros f.
    simpl.
    unfold Fail.
    do 2 f_equal.
    extensionality p.
    inversion p.
  Qed.

  Theorem Lzero : forall (f : A -> Prog A), Eq_Prog eq (Fail >>= f) Fail.
    intros f.
    rewrite Lzero'.
    reflexivity.
  Qed.

  Theorem Ldistr : forall p1 p2 (f : A -> Prog A), (p1 ? p2) >>= f = ((p1 >>= f) ? (p2 >>= f)).
    Admitted.

  Theorem T__Fail_fstrict : forall (f' : bool -> Prog bool),
      Eq_Prog eq (Share Fail >>= fun fx => fx >>= f') (pure Fail >>= fun fx => fx >>= f').
  Proof. econstructor. Qed.

  Theorem T__Fail_id :
    Eq_Prog eq (Share Fail >>= id) (pure Fail >>= id).
  Proof. econstructor. Qed.

  Definition const A B (x : A) (y : B) := x.

  Theorem State_ND_independence : forall n m (p : Prog A),
      runState n p = runState m p.
  Proof.
    intros n m p.
    induction p using Free_Share_Ind.
    - reflexivity.
    - reflexivity.
    - simpl.
      rewrite IHp1.
      rewrite IHp2.
      reflexivity.
  Qed.

  Theorem T__Fail_const : forall x,
      Eq_Prog eq (Share Fail >>= const x) (pure (@Fail A) >>= const x).
  Proof. 
    intros x. unfold const.
    unfold Eq_Prog, handle, Search.collectVals, Share', const. simpl.
    do 2 (rewrite nf_impure; simpl).
    simpl.
    rewrite State_ND_independence with (m := 1).
    reflexivity.
  Qed.
End SharingLaws.