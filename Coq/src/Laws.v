Require Import Thesis.Effect.
Require Import Thesis.Classes.
Require Import Thesis.DataM.
Require Import Thesis.Handler.
Require Import Thesis.Prog.
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
    { exists id p1 p2, p = Effect.Choice id p1 p2}.

Section Free_Share_Ind.
  Variable A : Type.
  Variable P : Prog A -> Prop.

  Hypothesis HPure : forall (x : A), P (pure x).
  Hypothesis HFail : P Fail.
  Hypothesis HChoice : forall id (p1 p2 : Prog A), P p1 -> P p2 -> P (Effect.Choice id p1 p2).

  Lemma Free_Share_Ind : forall (p : Prog A), P p.
  Proof.
    intros p.
    induction p using Free_Ind; eauto.
    destruct (Free_Share_dec (impure (ext s pf))) as [H1 | Hchoice].
    - destruct H1 as [Hpure | Hfail].
      + destruct Hpure as [x Hx]; discriminate Hx.
      + rewrite Hfail; eauto.
    - destruct Hchoice as [cid [p1 [p2 H12]]]; rewrite H12.
      dependent destruction H12.
      apply HChoice.
      + apply (H true).
      + apply (H false).
  Defined.
End Free_Share_Ind.

Section SharingLaws.
  Variable (A B C : Type).
  Variable nf__A : Normalform A A.
  Variable nf__B : Normalform B B.
  Variable nf__C : Normalform C C.
  Variable s__A : Shareable A.

  Theorem Lret : forall (f : A -> Prog B) (x : A), Eq_Prog _ (pure x >>= f) (f x).
  Proof. reflexivity. Qed.
  
  Theorem Rret : forall (p : Prog A), Eq_Prog _ (p >>= pure) p.
  Proof.
    intros p.
    rewrite bind_pure.
    reflexivity.
  Qed.

  Theorem Bassc : forall (p : Prog A) (f : A -> Prog B) (g : B -> Prog C),
      Eq_Prog _ ((p >>= f) >>= g) (p >>= fun x => f x >>= g).
  Proof.
    intros p f g.
    rewrite free_bind_assoc.
    reflexivity.
  Qed.

  Theorem Lzero : forall (f : A -> Prog B), Eq_Prog _ (Fail >>= f) Fail.
    intros f.
    unfold Eq_Prog, Fail.
    simpl.
    repeat f_equal.
    extensionality p.
    contradiction.
  Qed.

  Theorem Ldistr : forall p1 p2 (f : A -> Prog B),
      Eq_Prog _ ((p1 ? p2) >>= f) ((p1 >>= f) ? (p2 >>= f)).
  Proof.
    intros p1 p2 f.
    unfold Eq_Prog, Effect.Choice.
    simpl.
    do 3 f_equal.
    extensionality p.
    destruct p; reflexivity.
  Qed.

 Theorem Fail : Eq_Prog _ (Share Fail) (pure Fail).
 Proof.
   intros.
   unfold Eq_Prog, Share, Fail, handle.
   simpl.
   unfold nf'__Prog.
   simpl.
   do 4 (rewrite nf_impure; simpl).
   reflexivity.
 Qed.

 Lemma nf_bind : forall A B (p : Prog A) (f : A -> Prog B) `(Normalform A A) `(Normalform B B),
     nf (free_bind' f p) = free_bind' (fun x => nf (f x)) p.
 Proof.
   intros.
   induction p using Free_Ind.
   - reflexivity.
   - simpl.
     rewrite nf_impure.
     do 2 f_equal.
     extensionality p.
     apply (H1 p).
 Qed.

 Theorem Choice :
   forall (p1 p2 : Prog A),
     Eq_Prog _ (Share (p1 ? p2)) (Share p1 ? Share p2).
 Proof.
   intros.
   unfold Eq_Prog, handle.
   simpl.
   unfold nf'__Prog.
   repeat (rewrite nf_impure).
   unfold free_bind.
   repeat (rewrite nf_bind).
   simpl free_bind'.
 Admitted.
End SharingLaws.
