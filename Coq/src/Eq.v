Require Import Thesis.Prog.
Require Import Thesis.Classes.
Require Import Thesis.Handler.

Require Import Coq.Classes.RelationClasses.
Require Import Equivalence.

Set Implicit Arguments.

Section Eq_Prog.
  Variable A : Type.
  Variable NF__A : Normalform A A.

  Definition Eq_Prog (p1 p2 : Prog A) := handle p1 = handle p2.

  Lemma eq_Prog_refl : Reflexive Eq_Prog.
  Proof. 
    intros p.
    unfold Eq_Prog.
    reflexivity.
  Qed.

  Lemma eq_Prog_symm : Symmetric Eq_Prog.
  Proof.
    intros p1 p2 H.
    unfold Eq_Prog in *.
    symmetry.
    assumption.
  Qed.

  Lemma eq_Prog_trans : Transitive Eq_Prog.
  Proof.
    intros p1 p2 p3 H1 H2.
    unfold Eq_Prog in *.
    etransitivity.
    apply H1.
    assumption.
  Qed.

  Global Instance eq_Prog_Reflexive  : Reflexive Eq_Prog  := eq_Prog_refl.
  Global Instance eq_Prog_Symmetric  : Symmetric Eq_Prog  := eq_Prog_symm.
  Global Instance eq_Prog_Transitive : Transitive Eq_Prog := eq_Prog_trans.
End Eq_Prog.