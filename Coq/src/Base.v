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

  Definition Shape__Zero := Void.

  Definition Pos__Zero (s: Shape__Zero) := Void.

  Definition Ext__Zero A := Ext Shape__Zero Pos__Zero A.

  Definition to__Zero A (e: Ext__Zero A) : Zero A :=
    match e with
      ext s _ => match s with end
    end.

  Definition from__Zero A (z: Zero A) : Ext__Zero A :=
    match z with end.

  Lemma to_from__Zero : forall A (ox : Zero A), to__Zero (from__Zero ox) = ox.
  Proof.
    intros A ox.
    destruct ox.
  Qed.

  Lemma from_to__Zero : forall A (e : Ext__Zero A), from__Zero (to__Zero e) = e.
  Proof.
    intros A [s pf].
    destruct s.
  Qed.

  Instance C__Zero : Container Zero :=
    {
      Shape := Shape__Zero;
      Pos   := Pos__Zero;
      to    := to__Zero;
      from  := from__Zero;
      to_from := to_from__Zero;
      from_to := from_to__Zero
    }.

  Definition run A (fz : Free C__Zero A) : A :=
    match fz with
    | pure x => x
    | impure e => match e with
                    ext s _ => match s with end
                  end
    end.

End Zero.


Section Choice.

  Inductive Choice (A : Type) :=
  | cfail   : Choice A
  | cchoice : A -> A -> Choice A.

  Inductive Shape__Choice :=
  | sfail : Shape__Choice
  | schoice : Shape__Choice.

  Definition Pos__Choice (s: Shape__Choice) : Type :=
    match s with
    | sfail  => Void
    | schoice => bool
    end.

  Definition Ext__Choice A := Ext Shape__Choice Pos__Choice A.

  Definition to__Choice A (e: Ext__Choice A) : Choice A :=
    match e with
    | ext sfail f   => cfail A
    | ext schoice f => cchoice (f true) (f false)
    end.

  Fixpoint from__Choice A (z : Choice A) : Ext__Choice A :=
    match z with
    | cfail _     => ext sfail   (fun p : Pos__Choice sfail => match p with end)
    | cchoice l r => ext schoice (fun p : Pos__Choice schoice => if p then l else r)
    end.

  Lemma to_from__Choice : forall A (ox : Choice A), to__Choice (from__Choice ox) = ox.
  Proof.
    intros A ox.
    destruct ox; reflexivity.
  Qed.

  Lemma from_to__Choice : forall A (e : Ext__Choice A), from__Choice (to__Choice e) = e.
  Proof.
    intros A [s pf].
    destruct s; simpl; f_equal; apply functional_extensionality; intros x.
    - contradiction.
    - destruct x; reflexivity.
  Qed.
      
  Instance C__Choice : Container Choice :=
    {
      Shape := Shape__Choice;
      Pos   := Pos__Choice;
      to    := to__Choice;
      from  := from__Choice;
      to_from := to_from__Choice;
      from_to := from_to__Choice
    }.

  Fixpoint runChoice A (fc : Free C__Choice A) : list A :=
    match fc with
    | pure x => cons x nil
    | impure (ext sfail   _)  => nil
    | impure (ext schoice pf) => app (runChoice (pf true)) (runChoice (pf false))
    end.

  Definition Fail A : Free C__Choice A :=
    impure (ext sfail (fun p : Pos__Choice sfail => match p with end)).

  Arguments Fail {_}.

  Definition Choice' A l r : Free C__Choice A :=
    impure (ext schoice (fun p : Pos__Choice schoice => if p then l else r)).

End Choice.

Section State.

  Variable S : Type.

  Inductive State (A : Type) :=
  | get : (S -> A) -> State A
  | put : S -> A -> State A.

  Inductive Shape__State :=
  | sget : Shape__State
  | sput : S -> Shape__State.
  
  Inductive Pos__State : Shape__State -> Type :=
  | pget : forall (st : S), Pos__State sget
  | pput : forall (st : S), Pos__State (sput st).

  Definition Ext__State A := Ext Shape__State Pos__State A.

  Definition to__State (A : Type) (e: Ext__State A) : State A :=
    match e with
    | ext sget     fp => get (fun s => fp (pget s))
    | ext (sput s) fp => put s (fp (pput s))
    end.

  Fixpoint from__State A (z : State A) : Ext__State A :=
    match z with
    | get f   => ext sget     (fun p : Pos__State sget => match p with pget s => f s end)
    | put s a => ext (sput s) (fun p : Pos__State (sput s) => a)
    end.

  Lemma to_from__State : forall A (ox : State A), to__State (from__State ox) = ox.
  Proof.
    intros A ox.
    destruct ox.
    - simpl. f_equal.
    - reflexivity.
  Qed.

  Lemma from_to__State : forall A (e : Ext__State A), from__State (to__State e) = e.
  Proof.
    intros A [s pf].
    destruct s;
      (simpl;
       f_equal;
       apply functional_extensionality;
       intros p;
       dependent destruction p;
       reflexivity).
  Qed.

  Instance C__State : Container State :=
    {
      Shape := Shape__State;
      Pos   := Pos__State;
      to    := to__State;
      from  := from__State;
      to_from := to_from__State;
      from_to := from_to__State
    }.

  Fixpoint runState A (s : S) (fc : Free C__State A) : S * A :=
    match fc with
    | pure x => (s,x)
    | impure (ext sget      pf) => runState s  (pf (pget s))
    | impure (ext (sput s') pf) => runState s' (pf (pput s'))
    end.

  Definition Get (A : Type) : Free C__State S :=
    impure (ext sget (fun p : Pos__State sget => match p with pget s => pure s end)).

  Arguments Get {_}.

  Definition Put (A : Type) (s : S) : Free C__State unit :=
    impure (ext (sput s) (fun p : Pos__State (sput s) => match p with pput s => pure tt end)).

  Arguments Put {_} s.
End State.

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
