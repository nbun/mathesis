Require Import Thesis.HigherOrder.Container.
Set Implicit Arguments.

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

