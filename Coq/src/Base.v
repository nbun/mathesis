Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Inductive Ext Shape (Pos : Shape -> Type) A := ext : forall s, (Pos s -> A) -> Ext Shape Pos A.

Arguments ext {_} {_} {_} s pf.
Set Implicit Arguments.

Class Container F :=
  {
    Shape   : Type;
    Pos     : Shape -> Type;
    to      : forall A, Ext Shape Pos A -> F A;
    from    : forall A, F A -> Ext Shape Pos A;
    to_from : forall A (fx : F A), to (from fx) = fx;
    from_to : forall A (e : Ext Shape Pos A), from (to e) = e
  }.

Arguments from {_} {_} {_} _.

Section Free.
  Variable F : Type -> Type.

  Inductive Free (C__F : Container F) A :=
  | pure : A -> Free C__F A
  | impure : Ext Shape Pos (Free C__F A) -> Free C__F A.

End Free.

Arguments pure {_} {_} {_} _.

Section Zero.
  Inductive Void :=.

  Definition Zero (A : Type) := Void.

  Definition Shape_Zero := Void.

  Definition Pos_Zero (s: Shape_Zero) := Void.

  Definition Ext_Zero A := Ext Shape_Zero Pos_Zero A.

  Definition to_Zero A (e: Ext_Zero A) : Zero A :=
    match e with
      ext s _ => match s with end
    end.

  Definition from_Zero A (z: Zero A) : Ext_Zero A :=
    match z with end.

  Lemma to_from_Zero : forall A (ox : Zero A), to_Zero (from_Zero ox) = ox.
  Proof.
    intros.
    destruct ox.
  Qed.

  Lemma from_to_Zero : forall A (e : Ext_Zero A), from_Zero (to_Zero e) = e.
  Proof.
    intros.
    destruct e.
    destruct s.
  Qed.

  Instance C_Zero : Container Zero :=
    {
      Shape := Shape_Zero;
      Pos   := Pos_Zero;
      to    := to_Zero;
      from  := from_Zero;
      to_from := to_from_Zero;
      from_to := from_to_Zero
    }.
End Zero.

Definition run A (fz : Free C_Zero A) : A :=
  match fz with
    | pure x => x
    | impure e => match e with
                    ext s _ => match s with end
                  end
  end.

Section Choice.

  Inductive Choice (A : Type) :=
  | cfail   : Choice A
  | cchoice : Choice A -> Choice A -> Choice A.

  Inductive Tree :=
  | sleaf : Tree
  | snode : Tree -> Tree -> Tree.

  Fixpoint treeToChoice A (t : Tree) : Choice A :=
    match t with
    | sleaf => cfail A
    | snode x y => cchoice (treeToChoice A x) (treeToChoice A y)
    end.

  Fixpoint choiceToTree A (c : Choice A) : Tree :=
    match c with
    | cfail _ => sleaf
    | cchoice x y => snode (choiceToTree x) (choiceToTree y)
    end.

  Inductive Path :=
  | phere  : Path
  | pleft  : Path -> Path
  | pright : Path -> Path.

  Definition Shape_Choice := Tree.

  Definition Pos_Choice (s: Shape_Choice) := Path.

  Definition Ext_Choice A := Ext Shape_Choice Pos_Choice A.

  Definition to_Choice A (e: Ext_Choice A) : Choice A :=
    match e with
      ext s _ => match s with
                 | sleaf => cfail A
                 | snode x y => cchoice (treeToChoice A x) (treeToChoice A y)
                 end
    end.

  Fail Definition from_Choice A (z : Choice A) : Ext_Choice A :=
    match z with
    | cfail _ => ext sleaf (fun p : Pos_Choice sleaf => match p with
                                                        | phere     => 42
                                                        | pleft p'  => 42
                                                        | pright p' => 42
                                                        end)
    | cchoice l r => ext (snode (choiceToTree l) (choiceToTree r)) (fun p => 42)
    end.
End Choice.

(*
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

  Variable F : Type -> Type.
  Variable C__F : Container F.

  Definition cmap A B (f : A -> B) (x : Ext Shape Pos A) : Ext Shape Pos B :=
    match x with
    | ext s pf => ext s (fun x => f (pf x))
    end.

  Section fbind.

    Variable A B: Type.
    Variable f: A -> Free C__F B.

    Fixpoint free_bind' (ffA: Free C__F A) :=
      match ffA with
      | pure x => f x
      | impure e => impure (cmap free_bind' e)
      end.

  End fbind.

  Definition free_bind A B (ffA: Free C__F A) (f: A -> Free C__F B) : Free C__F B :=
    free_bind' f ffA.

  Notation "mx >>= f" := (free_bind mx f) (at level 50, left associativity).
  Notation "'do' x <- mx ; f" :=
    (free_bind mx (fun x => f))
      (at level 50, x ident, mx at level 40, f at level 50).

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
    - simpl free_bind.
      repeat apply f_equal.
      apply functional_extensionality.
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

  Global Instance free_monad : Monad (Free C__F) :=
    {
      ret := @pure F C__F;
      bind := fun _ _ xs f => free_bind xs f;
      left_unit := pure_bind;
      right_unit := bind_pure;
      bind_assoc := free_bind_assoc
    }.

End MonadInstance.
Arguments cmap {_} {_} {_} {_}.

Notation "mx >>= f" := (free_bind mx f) (at level 50, left associativity).
Notation "'do' x <- mx ; f" :=
  (free_bind mx (fun x => f))
    (at level 50, x ident, mx at level 40, f at level 50).

Section MonadInstances.

  Definition Id (A : Type) := A.

  Definition id_ret A (x : A) : Id A :=
    x.

  Definition id_bind A B (a : Id A) (f : A -> Id B) : Id B := f a.

  Lemma id_left_identity :
    forall A B (a : A) (f : A -> Id B),
      id_bind (id_ret a) f = f a.
  Proof.
    repeat intro.
    unfold id_ret.
    unfold id_bind.
    reflexivity.
  Qed.

  Lemma id_right_identity :
    forall A (ia : Id A),
      id_bind ia (fun a => id_ret a) = ia.
  Proof.
    repeat intro.
    unfold id_bind.
    unfold id_ret.
    reflexivity.
  Qed.

  Lemma id_associativity :
    forall A B C (ia : Id A) (f : A -> Id B) (g : B -> Id C),
      id_bind ia (fun a => id_bind (f a) g) = id_bind (id_bind ia f) g.
  Proof.
    repeat intro.
    unfold id_bind.
    reflexivity.
  Qed.

  Global Instance id_monad : Monad Id :=
    {
      ret := id_ret;
      bind := id_bind;
      left_unit := id_left_identity;
      right_unit := id_right_identity;
      bind_assoc := id_associativity
    }.

  Inductive Maybe A :=
  | nothing : Maybe A
  | just : A -> Maybe A.

  Global Arguments nothing {_}.

  Definition maybe_ret A (a : A) : Maybe A :=
    just a.

  Definition maybe_bind A B (ma : Maybe A) (f : A -> Maybe B) : Maybe B :=
    match ma with
    | nothing => nothing
    | just a => f a
    end.

  Lemma maybe_left_identity :
    forall A B (a : A) (f : A -> Maybe B),
      maybe_bind (maybe_ret a) f = f a.
  Proof.
    reflexivity.
  Qed.

  Lemma maybe_right_identity :
    forall A (ma : Maybe A),
      maybe_bind ma (@maybe_ret A) = ma.
  Proof.
    induction ma.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma maybe_associativity :
    forall A B C (ma : Maybe A) (f : A -> Maybe B) (g : B -> Maybe C),
      maybe_bind ma (fun a => maybe_bind (f a) g) = maybe_bind (maybe_bind ma f) g.
  Proof.
    intros.
    induction ma.
    - reflexivity.
    - reflexivity.
  Qed.

  Global Instance maybe_monad : Monad Maybe :=
    {
      ret := maybe_ret;
      bind := maybe_bind;
      left_unit := maybe_left_identity;
      right_unit := maybe_right_identity;
      bind_assoc := maybe_associativity
    }.

End MonadInstances.

Section FunctorClass.

  Class Functor (F: Type -> Type) :=
    {
      fmap : forall A B, (A -> B) -> F A -> F B;
      fmap_id : forall A (fx : F A), fmap (fun x => x) fx = fx;
      fmap_comp : forall A B C (f : B -> C) (g : A -> B) (fx : F A),
          fmap f (fmap g fx) = fmap (fun x => f (g x)) fx
    }.

End FunctorClass.
*)
