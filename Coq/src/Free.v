(** Definition of the free monad, a stronger induction principle,
    monad operations and proofs of the monad laws *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Import Thesis.Container.

Set Implicit Arguments.

(** Definition of the free monad based on containers to
    represent strictly positive functors *)
Section Free.

  Variable F : Type -> Type.

  Inductive Free (C__F : Container F) A :=
  | pure : A -> Free C__F A
  | impure : Ext Shape Pos (Free C__F A) -> Free C__F A.

End Free.

Arguments pure {_} {_} {_} _.

(** Leibniz's equality for Free *)
Section Free_Rect.

  Variable F : Type -> Type.
  Variable C__F : Container F.
  Variable A : Type.
  Variable P : Free C__F A -> Type.

  Variable Pure_rect : forall (x : A), P (pure x).
  Variable Impure_rect : forall (s : Shape) (pf : Pos s -> Free C__F A),
      (forall p, P (pf p)) -> P (impure (ext s pf)).

  Fixpoint Free_Rect (fx : Free C__F A) : P fx :=
    match fx with
    | pure x => Pure_rect x
    | impure (ext s pf) =>
      Impure_rect s pf (fun p : Pos s => Free_Rect (pf p))
    end.

End Free_Rect.

(** Stronger induction principle for Free *)
Section Free_Ind.

  Variable F : Type -> Type.
  Variable C__F : Container F.
  Variable A : Type.
  Variable P : Free C__F A -> Prop.

  Variable Pure_ind : forall (x : A), P (pure x).
  Variable Impure_ind : forall (s : Shape) (pf : Pos s -> Free C__F A),
      (forall p, P (pf p)) -> P (impure (ext s pf)).

  Definition Free_Ind (fx : Free C__F A) : P fx := Free_Rect P Pure_ind Impure_ind fx.

End Free_Ind.

(** Definition of functor and monad operations *)
Section MonadInstance.

  Variable F : Type -> Type.
  Variable C__F : Container F.

  (** Corresponds to fmap *)
  Definition cmap A B (f : A -> B) (x : Ext Shape Pos A) : Ext Shape Pos B :=
    match x with
    | ext s pf => ext s (fun x => f (pf x))
    end.

  Section fbind.
    
    Variable A B: Type.
    Variable f: A -> Free C__F B.
    
    Fixpoint free_bind' (ffA: Free C__F A) : Free C__F B :=
      match ffA with
      | pure x => f x
      | impure e => impure (cmap free_bind' e)
      end.
    
  End fbind.

  Definition free_bind A B (ffA: Free C__F A) (f: A -> Free C__F B) : Free C__F B :=
    free_bind' f ffA.

  Notation "mx >>= f" := (free_bind mx f)  (at level 20, left associativity).

  (** Monad laws *)
  Lemma pure_bind :
    forall A B (x: A) (f: A -> Free C__F B), pure x >>= f = f x.
  Proof.
    reflexivity.
  Qed.
  
  Lemma bind_pure :
    forall A (fA: Free C__F A), fA >>= (fun x => pure x) = fA.
  Proof.
    induction fA using Free_Ind.
    - reflexivity.
    - simpl.
      do 2 f_equal.
      extensionality p.
      apply H.
  Qed.

  Lemma free_bind_assoc :
    forall A B C (fa : Free C__F A) (f: A -> Free C__F B) (g: B -> Free C__F C),
      fa >>= (fun y => f y >>= g) = fa >>= f >>= g.
  Proof.
    intros.
    induction fa using Free_Ind.
    - econstructor.
    - simpl free_bind.
      repeat apply f_equal.
      apply functional_extensionality.
      apply H.
  Qed.
End MonadInstance.

Arguments cmap {_} {_} {_} {_}.

(** Notations for bind and sequence that are visible when importing the module *)
Notation "mx >>= f" := (free_bind mx f) (at level 20, left associativity).
Notation "mx >>  f" := (free_bind mx (fun _ => f)) (at level 25, left associativity).
