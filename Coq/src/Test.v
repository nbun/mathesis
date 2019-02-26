Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Inductive Ext Shape (Pos : Shape -> Type -> Type -> Type) (F : Type -> Type) A :=
  ext : forall s, (forall X, Pos s A X -> F X) -> Ext Shape Pos F A.

Arguments ext {_} {_} {_} {_} s pf.

Set Implicit Arguments.

Class HContainer (H : (Type -> Type) -> Type -> Type):=
  {
    Shape   : Type;
    Pos     : Shape -> Type -> Type -> Type;
    to      : forall M A, Ext Shape Pos M A -> H M A;
    from    : forall M A, H M A -> Ext Shape Pos M A;
    to_from : forall M A (fx : H M A), @to M A (@from M A fx) = fx;
    from_to : forall M A (e : Ext Shape Pos M A), @from M A (@to M A e) = e
  }.

Arguments from {_} {_} {_} _.

Section Free.
  Variable H : (Type -> Type) -> Type -> Type.

  Inductive Free (HC__F : HContainer H) A :=
  | pure : A -> Free HC__F A
  | impure : Ext Shape Pos (Free HC__F) A -> Free HC__F A.
End Free.

Arguments pure {_} {_} {_} _.

(* lambda calculus *)

Inductive LC_F (F : Type -> Type) (A : Type) : Type :=
| App : F A -> F A -> LC_F F A
| Lam : F (sum unit A) -> LC_F F A.

Definition Shape__LC := bool.

Inductive App_F (A : Type) : Type -> Type :=
| App_ (s : Shape__LC) : App_F A A.

Inductive Lam_F (A : Type) : Type -> Type :=
| Lam_ : Lam_F A (sum unit A).

Definition Pos__LC (s : Shape__LC) : Type -> Type -> Type :=
  match s with
  | true => App_F
  | false => Lam_F
  end.

Definition Ext__LC F A := Ext Shape__LC Pos__LC F A.

Definition to__LC F A (e : Ext__LC F A) : LC_F F A.
  destruct e.
  destruct s.
  - apply App.
    + apply f.
      simpl.
      apply App_.
      apply true.
    + apply f.
      simpl.
      apply App_.
      apply false.
  - apply Lam.
    apply f.
    simpl.
    apply Lam_.
Defined.

Definition from__LC F A (z : LC_F F A) : Ext__LC F A.
  destruct z.
  - unfold Ext__LC.
    apply ext with (s := true).
    intros. simpl in X0.
    destruct X0.
    destruct s.
    + apply f.
    + apply f0.
  - unfold Ext__LC.
    apply ext with (s := false).
    intros.
    destruct X0.
    apply f.
Defined.
    
Lemma to_from__LC : forall F A (ox : LC_F F A), to__LC (from__LC ox) = ox.
Proof.
  intros F A ox.
  destruct ox; reflexivity.
Qed.

Lemma from_to__LC : forall F A (e : Ext__LC F A), from__LC (to__LC e) = e.
Proof.
  intros F A [s pf].
  destruct s;
    simpl;
    f_equal;
    extensionality X;
    extensionality b;
    destruct b.
  - destruct s; reflexivity.
  - reflexivity.
Qed.

Instance C__LC : HContainer LC_F :=
  {
    Shape := Shape__LC;
    Pos   := Pos__LC;
    to    := to__LC;
    from  := from__LC;
    to_from := to_from__LC;
    from_to := from_to__LC
  }.

Definition LC : Type -> Type := Free C__LC.

Definition App' {A} (x y : LC A) : LC A :=
  impure (ext true (fun _ f =>
    match f in App_F _ B return LC B with
    | App_ _ true => x
    | App_ _ false => y
    end)).

Definition Lam' {A} (x : LC (unit + A)) : LC A :=
  impure (ext false (fun _ f =>
    match f in Lam_F _ B return LC B with
    | Lam_ _ => x
    end)).

(* \x -> x*)
Definition id_lc {A} : LC A := Lam' (pure (inl tt)).

(* \f x -> f x x *)
Definition omega {A} : LC A :=
  Lam' (* f *) (Lam' (* x *)
    (let f := pure (inr (inl tt)) in
     let x := pure (inl tt) in
     App' (App' f x) x)).

(* exceptions *)

Inductive Exc F (A : Type) :=
| ccatch : forall X, F X -> (X -> F A) -> Exc F A.

Inductive Shape__Exc F :=
| scatch : forall (X : Type), F X -> Shape__Exc F.

Inductive Catch_F X (A : Type) : Type -> Type :=
| pcatch (x : X) : Catch_F X A A.

Definition Pos__Exc F (s : Shape__Exc F) : Type -> Type -> Type :=
  match s with
  | scatch _ X fx => Catch_F X
  end.

Definition Ext__Exc F A := Ext (Shape__Exc F) (@Pos__Exc F) F A.

Definition to__Exc F A (e: Ext__Exc F A) : Exc F A.
  destruct e.
  destruct s.
  apply ccatch with (X := X).
  - apply f0.
  - intros x.
    apply f.
    apply pcatch.
    apply x.
Defined.

Definition from__Exc F A (z : Exc F A) : Ext__Exc F A.
  destruct z.
  apply ext with (s := scatch F X f).
  intros X0.
  intros p.
  destruct p.
  apply f0.
  apply x.
Defined.
  
Lemma to_from__Exc : forall F A (ox : Exc F A), to__Exc (from__Exc ox) = ox.
Proof.
  intros F A ox.
  destruct ox; reflexivity.
Qed.

Lemma from_to__Exc : forall F A (e : Ext__Exc F A), from__Exc (to__Exc e) = e.
Proof.
  intros F A [s pf].
  destruct s;
    simpl;
    f_equal.
    extensionality X0;
    extensionality b;
    destruct b.
  - reflexivity.
Qed.

Fail Instance C__Exc (F : Type -> Type) : HContainer Exc :=
  {
    Shape := Shape__Exc F;
    Pos   := @Pos__Exc F;
    to    := to__Exc;
    from  := from__Exc;
    to_from := to_from__Exc;
    from_to := from_to__Exc
  }.
