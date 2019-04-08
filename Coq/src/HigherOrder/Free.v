(** Definition of the free monad for higher-order containers,
    a stronger induction principle, monad operations and proofs
    of the monad laws *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Import Thesis.HigherOrder.Container.

Set Implicit Arguments.

(** Definition of the free monad for higher-order containers *)
Section Free.

  Variable H : (Type -> Type) -> Type -> Type.

  Inductive Free (C : HContainer H) A :=
  | pure : A -> Free C A
  | impure : Ext Shape Pos PosX Ctx (Free C) A -> Free C A.

End Free.

Arguments pure {_ _ _} _.

Section Free_Rect.

  Variable H : (Type -> Type) -> Type -> Type.
  Variable C__H : HContainer H.
  Variable A : Type.
  Variable P : Free C__H A -> Type.

  Variable Pure_rect : forall (x : A), P (pure x).
  Variable Impure_rect : forall (s : Shape) (pf : Pos s -> Free C__H A) pfx,
      (forall p, P (pf p)) -> P (impure (ext s pf pfx)).

  Fixpoint Free_Rect (fx : Free C__H A) : P fx :=
    match fx with
    | pure x => Pure_rect x
    | impure (ext s pf pfx) =>
      Impure_rect s pf pfx (fun p : Pos s => Free_Rect (pf p))
    end.

End Free_Rect.

Section Free_Ind.

  Variable H : (Type -> Type) -> Type -> Type.
  Variable C__H : HContainer H.
  Variable A : Type.
  Variable P : Free C__H A -> Prop.

  Variable Pure_ind : forall (x : A), P (pure x).
  Variable Impure_ind : forall (s : Shape) (pf : Pos s -> Free C__H A) pfx,
      (forall p, P (pf p)) -> P (impure (ext s pf pfx)).

  Definition Free_Ind (fx : Free C__H A) : P fx := Free_Rect P Pure_ind Impure_ind fx.

End Free_Ind.

Section MonadInstance.

  Variable H : (Type -> Type) -> Type -> Type.
  Variable C__H : HContainer H.

  (** The function f is mapped over the position function that contains values of type A.
      The other position function is not modified since it cannot contain values of type A. *)
  Definition cmap A B F (f : F A -> F B) (x : Ext Shape Pos PosX Ctx F A) : Ext Shape Pos PosX Ctx F B :=
    match x with
    | ext s pf pfx => ext s (fun p : Pos s => f (pf p)) (fun p : PosX s => pfx p)
    end.

  Section fbind.

    Variable A B: Type.
    Variable f: A -> Free C__H B.
    Fixpoint free_bind' (ffA: Free C__H A) : Free C__H B :=
      match ffA with
      | pure a => f a
      | impure e => impure (cmap B (fun x => free_bind' x) e)
      end.

  End fbind.

  Definition free_bind A B (ffA: Free C__H A) (f: A -> Free C__H B) : Free C__H B :=
    free_bind' f ffA.

  Notation "mx >>= f" := (free_bind mx f) (at level 50, left associativity).

  Lemma pure_bind :
    forall A B (x: A) (f: A -> Free C__H B), pure x >>= f = f x.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_pure :
    forall A (fA: Free C__H A), fA >>= (fun x => pure x) = fA.
  Proof.
    induction fA using Free_Ind.
    - reflexivity.
    - simpl.
      do 2 f_equal.
      extensionality p.
      apply H0.
  Qed.

  Lemma free_bind_assoc :
    forall A B C (fa : Free C__H A) (f: A -> Free C__H B) (g: B -> Free C__H C),
      fa >>= (fun y => f y >>= g) = fa >>= f >>= g.
  Proof.
    intros.
    induction fa using Free_Ind.
    - econstructor.
    - simpl free_bind.
      repeat f_equal.
      apply functional_extensionality.
      apply H0.
  Qed.

End MonadInstance.
Arguments cmap {_} {_} {_} {_}.

Notation "mx >>= f" := (free_bind mx         f) (at level 20, left associativity).
Notation "mx >>  f" := (free_bind mx (fun _ => f)) (at level 20, left associativity).
