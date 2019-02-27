Require Import Thesis.HigherOrder.Container.
Set Implicit Arguments.

Section Free.

  Variable H : (Type -> Type) -> Type -> Type.

  Inductive Free (C : HContainer H) A :=
  | pure : A -> Free C A
  | impure : Ext Shape Pos Ctx (Free C) A -> Free C A.

End Free.

Arguments pure {_ _ _} _.

(* Section Free_Rect. *)

(*   Variable H : (Type -> Type) -> Type -> Type. *)
(*   Variable C__H : HContainer H. *)
(*   Variable F : Type -> Type. *)
(*   Variable A : Type. *)
(*   Variable P : Free C__H A -> Type. *)

(*   Variable Pure_rect : forall (x : A), P (pure x). *)
(*   Variable Impure_rect : forall (s : Shape) (pf : Pos s -> Free C__H A), *)
(*       (forall p, P (pf p)) -> P (impure (ext s pf)). *)

(*   Fixpoint Free_Rect (fx : Free C__F A) : P fx := *)
(*     match fx with *)
(*     | pure x => Pure_rect x *)
(*     | impure (ext s pf) => *)
(*       Impure_rect s pf (fun p : Pos s => Free_Rect (pf p)) *)
(*     end. *)

(* End Free_Rect. *)

(* Section Free_Ind. *)

(*   Variable F : Type -> Type. *)
(*   Variable C__F : Container F. *)
(*   Variable A : Type. *)
(*   Variable P : Free C__F A -> Prop. *)

(*   Variable Pure_ind : forall (x : A), P (pure x). *)
(*   Variable Impure_ind : forall (s : Shape) (pf : Pos s -> Free C__F A), *)
(*       (forall p, P (pf p)) -> P (impure (ext s pf)). *)

(*   Definition Free_Ind (fx : Free C__F A) : P fx := Free_Rect P Pure_ind Impure_ind fx. *)

(* End Free_Ind. *)

