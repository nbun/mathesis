Require Import Thesis.Prog.
Require Import Thesis.Classes.
Require Import Thesis.Handler.

Require Import Coq.Classes.RelationClasses.
Require Import Equivalence.

Set Implicit Arguments.

Section Eq_list.
  Variable A : Type.
  Variable eq_A : A -> A -> Prop.
  
  Variable eq_A_refl  : Reflexive eq_A.
  Variable eq_A_symm  : Symmetric eq_A.
  Variable eq_A_trans : Transitive eq_A.
  
  Inductive Eq_list : list A -> list A -> Prop :=
  | eq_nil  : Eq_list nil nil
  | eq_cons : forall x y xs ys,
      eq_A x y ->
    Eq_list xs ys ->
    Eq_list (cons x xs) (cons y ys).
  
  Lemma eq_list_refl : Reflexive Eq_list.
  Proof.
    intros xs.
    induction xs as [ | y ys].
    - constructor.
    - constructor.
      + reflexivity.
      + assumption.
  Qed.

  Lemma eq_list_symm : Symmetric Eq_list.
  Proof.
    intros xs ys H.
    induction H; constructor.
    - symmetry. assumption.
    - assumption.
  Qed.

  Lemma eq_list_trans : Transitive Eq_list.
  Proof with auto; try constructor; auto.
    intros xs.
    induction xs; intros ys zs H1 H2; inversion H1; subst; inversion H2; subst...
    - etransitivity. apply H3. assumption.
    - apply IHxs with (y := ys0); assumption.
  Qed.

  Global Instance eq_list_Reflexive : Reflexive Eq_list := eq_list_refl.
  Global Instance eq_list_Symmetric : Symmetric Eq_list := eq_list_symm.
  Global Instance eq_list_Transitive : Transitive Eq_list := eq_list_trans.

  Definition Eq_Prog `{Normalform A A} (p1 p2 : Prog A) :=
    Eq_list (handle p1) (handle p2).

  Variable nf__A : (Normalform A A).
  Lemma eq_Prog_refl : Reflexive Eq_Prog.
  Proof. 
    intros p.
    unfold Eq_Prog.
    reflexivity.
  Qed.

  Lemma eq_Prog_symm : Symmetric Eq_Prog.
  Proof.
    intros p1 p2 H.
    unfold Eq_Prog.
    unfold Eq_Prog in H.
    symmetry.
    assumption.
  Qed.

  Lemma eq_Prog_trans : Transitive Eq_Prog.
  Proof.
    intros p1 p2 p3 H1 H2.
    unfold Eq_Prog.
    unfold Eq_Prog in H1, H2.
    etransitivity.
    apply H1.
    assumption.
  Qed.

  Global Instance eq_Prog_Reflexive : Reflexive Eq_Prog := eq_Prog_refl.
  Global Instance eq_Prog_Symmetric : Symmetric Eq_Prog := eq_Prog_symm.
  Global Instance eq_Prog_Transitive : Transitive Eq_Prog := eq_Prog_trans.

End Eq_list.
