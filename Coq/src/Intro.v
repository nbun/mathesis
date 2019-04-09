(** Examples and definitions from the Coq introduction *)
Require Import Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Import Equivalence.
Require Import Lists.List.
Require Import Program.

Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Inductive List A : Type :=
| nil  : List A
| cons : option A -> option (List A) -> List A.

Definition empty A := @cons A None None.

Definition head A (oxs : List A) : option A :=
  match oxs with
  | nil       => None
  | cons ox _ => ox
  end.

Fail Fixpoint app A (oxs oys : option (List A)) : option (List A) :=
  match oxs with
  | None    => None
  | Some xs =>
    match xs with
    | nil         => oys
    | cons oz ozs => Some (cons oz (app ozs oys))
    end
  end.

Definition bind A B (o : option A) (f : A -> option B) : option B :=
  match o with
  | None   => None
  | Some x => f x
  end.

Fixpoint app' A (xs : List A) (oys : option (List A)) : option (List A) :=
  match xs with
  | nil => oys
  | cons oz ozs => Some (cons oz (bind ozs (fun zs => app' zs oys)))
  end.

Definition app A (oxs oys : option (List A)) : option (List A) :=
  bind oxs (fun xs => app' xs oys).

Fail Fixpoint quicksort (xs : list nat) {struct xs} : list nat :=
  match xs with
  | nil => nil
  | cons y ys =>
    let le x := Nat.leb x y in
    let gt x := negb (Nat.ltb x y)
    in quicksort (filter le ys) ++ [y] ++ quicksort (filter gt ys)
  end.

Lemma eq11 : 1 = 1.
Proof. reflexivity. Qed.

Locate "=".
Print eq.

Program Fixpoint quicksort (xs : list nat) {measure (length xs)} : list nat :=
  match xs with
  | List.nil => List.nil
  | List.cons y ys =>
    let le x := Nat.leb x y in
    let gt x := negb (Nat.ltb x y)
    in quicksort (filter le ys) ++ [y] ++ quicksort (filter gt ys)
  end.

Lemma filter_length:
  forall (A : Type) (xs : list A) (p : A -> bool),
    length (filter p xs) <= length xs.
Proof.
  intros A xs p.
  induction xs; simpl.
  - reflexivity.
  - destruct (p a); simpl.
    + apply le_n_S.
      apply IHxs.
    + apply le_S.
      apply IHxs.
Qed.

Next Obligation.
  simpl.
  apply Lt.le_lt_n_Sm.
  apply filter_length.
Qed.

Next Obligation.
  simpl.
  apply Lt.le_lt_n_Sm.
  apply filter_length.
Qed.

Compute quicksort [23; 8; 15; 4; 42; 16].

Inductive Vec (A : Type) : nat -> Type :=
| vnil  : Vec A 0
| vcons : forall n, A -> Vec A n -> Vec A (S n).

Definition vlength (A : Type) (n : nat) (xs : Vec A n) : nat := n.

Compute vlength (vcons true (vcons true vnil)).
Fail Compute @vlength bool 2 (vcons true vnil).

Fixpoint vapp (A : Type) (n m : nat) (xs : Vec A n) (ys : Vec A m) : Vec A (n + m) :=
  match xs with
  | vnil       => ys
  | vcons z zs => vcons z (vapp zs ys)
  end.

Definition vhead (A : Type) (n : nat) (xs : Vec A (S n)) : A.
  dependent destruction xs.
  apply a.
Defined.
