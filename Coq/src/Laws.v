Require Import Thesis.Effect.
Require Import Thesis.Classes.
Require Import Thesis.DataM.
Require Import Thesis.Handler.
Require Import Thesis.Prog.
Require Import Thesis.Base.
Require Import Thesis.Eq.

Require Import Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Import Equivalence.


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
  Variable s__A : Shareable A.
  Variable eqA : A -> A -> Prop.

  Variable eqA_refl  : Reflexive eqA.
  Variable eqA_symm  : Symmetric eqA.
  Variable eqA_trans : Transitive eqA.

  Theorem Lret : forall f (x : A), Eq_Prog eqA (pure x >>= f) (f x).
  Proof. reflexivity. Qed.
  
  Theorem Rret : forall (p : Prog A), Eq_Prog eqA (p >>= pure) p.
  Proof.
    intros p.
    rewrite bind_pure.
    reflexivity.
  Qed.

  Theorem Bassc : forall (p : Prog A) (f g : A -> Prog A), Eq_Prog eqA ((p >>= f) >>= g) (p >>= fun x => f x >>= g).
  Proof.
    intros p f g.
    rewrite free_bind_assoc.
    reflexivity.
  Qed.

  Lemma Lzero' : forall (f : A -> Prog A), (Fail >>= f) = Fail.
    intros f.
    simpl.
    unfold Fail.
    do 2 f_equal.
    extensionality p.
    inversion p.
  Qed.

  Theorem Lzero : forall (f : A -> Prog A), Eq_Prog eqA (Fail >>= f) Fail.
    intros f.
    rewrite Lzero'.
    reflexivity.
  Qed.

  Lemma Ldistr' : forall p1 p2 (f : A -> Prog A), ((p1 ? p2) >>= f) = ((p1 >>= f) ? (p2 >>= f)).
  Proof.
    intros p1 p2 f.
    unfold Effect.Choice.
    simpl.
    do 2 f_equal.
    extensionality p.
    destruct p; reflexivity.
  Qed.

  Theorem Ldistr : forall p1 p2 (f : A -> Prog A), Eq_Prog eqA ((p1 ? p2) >>= f) ((p1 >>= f) ? (p2 >>= f)).
  Proof.
    intros p1 p2 f.
    rewrite Ldistr'.
    reflexivity.
  Qed.

  Theorem T__Fail_fstrict : forall (f' : A -> Prog A),
      Eq_Prog eqA (Share Fail >>= fun fx => fx >>= f') (pure Fail >>= fun fx => fx >>= f').
  Proof. 
    intros f'.
    unfold Eq_Prog, handle, Search.collectVals, Share'.
    simpl.
    repeat (rewrite nf_impure; simpl).
    econstructor.
  Qed.

  (* Mark id as volatile to enable automatic unfolding *)
  Arguments id / A x.

  Theorem T__Fail_id :
    Eq_Prog eqA (Share Fail >>= id) (pure Fail >>= id).
  Proof.
    unfold Eq_Prog, handle, Search.collectVals, Share', Fail.
    simpl.
    repeat (rewrite nf_impure; try unfold Share'; simpl).
    constructor.
  Qed.

  Definition const A B (x : A) (y : B) := x.

  (* Mark const as volatile to enable automatic unfolding *)
  Arguments const / A B x y.

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
      Eq_Prog eqA (Share Fail >>= const x) (pure (@Fail A) >>= const x).
  Proof. 
    intros x. 
    unfold Eq_Prog, handle, Search.collectVals, Share'. simpl.
    do 2 (rewrite nf_impure; simpl).
    rewrite State_ND_independence with (m := 1).
    reflexivity.
  Qed.
End SharingLaws.