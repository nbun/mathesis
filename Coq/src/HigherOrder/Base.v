Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Thesis.HigherOrder.Container.
Require Import Thesis.HigherOrder.Free.

Set Implicit Arguments.

Section MonadClass.

  Class Monad (M: Type -> Type) :=
    {
      ret : forall A, A -> M A;
      bind : forall A B, M A -> (A -> M B) -> M B;
      left_unit : forall A B (x0: A) (f: A -> M B),
                    bind (ret x0) f = f x0;
      right_unit : forall A (ma: M A), bind ma (@ret A) = ma;
      bind_assoc: forall A B C (ma : M A) (f: A -> M B) (g: B -> M C),
                    bind ma (fun y => bind (f y) g) = bind (bind ma f) g
    }.

  Definition join (M: Type -> Type) `(Monad M) A (mmx : M (M A)) : M A := bind _ mmx (fun x => x).

End MonadClass.
Arguments join {_} {_} {_}.

Section MonadInstance.

  Variable H : (Type -> Type) -> Type -> Type.
  Variable C__H : HContainer H.

  Definition cmap A B F (f : F A -> F B) (x : Ext Shape Pos PosX Ctx F A) : Ext Shape Pos PosX Ctx F B.
    destruct x.
    apply ext with (s0 := s).
    - intros.
      apply f.
      apply f0.
      apply X.
    - intros.
      apply f1.
  Defined.

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

  Global Instance free_monad : Monad (Free C__H) :=
    {
      ret := @pure H C__H;
      bind := fun _ _ xs f => free_bind xs f;
      left_unit := pure_bind;
      right_unit := bind_pure;
      bind_assoc := free_bind_assoc
    }.

End MonadInstance.
Arguments cmap {_} {_} {_} {_}.

Notation "mx >>= f" := (free_bind mx f) (at level 50, left associativity).
