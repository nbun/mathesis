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


Definition hf (F G : Type -> Type) := forall X, F X -> G X.
Notation "F --> G" := (hf F G) (at level 42).

Class HFunctor (H : (Type -> Type) -> Type -> Type) :=
  {
    hmap : forall F G, F --> G -> (H F --> H G)
  }.

Class Syntax (H : (Type -> Type) -> Type -> Type) :=
  {
    emap : forall F A B, (F A -> F B) -> (H F A -> H F B)
  }.

Section MonadInstance.

  Variable H : (Type -> Type) -> Type -> Type.
  Variable HF : Syntax H.
  Variable C__H : HContainer H.

  (* Definition cmap A B F (f : F A -> F B) (x : Ext Shape Pos Ctx F A) : Ext Shape Pos Ctx F B. *)
  (*   destruct x. *)
  (*   apply ext with (s0 := s). *)
  (*   intros. *)
  (*   specialize f0 with p. *)
    

  Section fbind.

    Variable A B: Type.
    Variable f: A -> Free C__H B.

    Fixpoint free_bind' (ffA: Free C__H A) : Free C__H B.
      destruct ffA.
      - apply f, a.
      - apply impure.
        apply from.
        eapply emap.
        + apply free_bind'.
        + apply to.
          apply e.
    Admitted.
      (* match ffA with *)
      (* | pure x => g x *)
      (* | impure e => impure (emap _ _ _ (free_bind' g) e) *)
      (* end. *)

  End fbind.
End MonadInstance.

(*   Definition free_bind A B (ffA: Free C__F A) (f: A -> Free C__F B) : Free C__F B := *)
(*     free_bind' f ffA. *)

(*   Notation "mx >>= f" := (free_bind mx f) (at level 50, left associativity). *)
(*   (* Notation "'do' x <- mx ; f" := *) *)
(*   (*   (free_bind mx (fun x => f)) *) *)
(*   (*     (at level 50, x ident, mx at level 40, f at level 50). *) *)

(*   Lemma pure_bind : *)
(*     forall A B (x: A) (f: A -> Free C__F B), pure x >>= f = f x. *)
(*   Proof. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Lemma bind_pure : *)
(*     forall A (fA: Free C__F A), fA >>= (fun x => pure x) = fA. *)
(*   Proof. *)
(*     induction fA using Free_Ind. *)
(*     - reflexivity. *)
(*     - simpl. *)
(*       do 2 f_equal. *)
(*       extensionality p. *)
(*       apply H. *)
(*   Qed. *)

(*   Lemma free_bind_assoc : *)
(*     forall A B C (fa : Free C__F A) (f: A -> Free C__F B) (g: B -> Free C__F C), *)
(*       fa >>= (fun y => f y >>= g) = fa >>= f >>= g. *)
(*   Proof. *)
(*     intros. *)
(*     induction fa using Free_Ind. *)
(*     - econstructor. *)
(*     - simpl free_bind. *)
(*       repeat apply f_equal. *)
(*       apply functional_extensionality. *)
(*       apply H. *)
(*   Qed. *)

(*   Global Instance free_monad : Monad (Free C__F) := *)
(*     { *)
(*       ret := @pure F C__F; *)
(*       bind := fun _ _ xs f => free_bind xs f; *)
(*       left_unit := pure_bind; *)
(*       right_unit := bind_pure; *)
(*       bind_assoc := free_bind_assoc *)
(*     }. *)

(* End MonadInstance. *)
(* Arguments cmap {_} {_} {_} {_}. *)

(* Notation "mx >>= f" := (free_bind mx f) (at level 50, left associativity). *)
(* (* Notation "'do' x <- mx ; f" := *) *)
(* (*   (free_bind mx (fun x => f)) *) *)
(* (*     (at level 50, x ident, mx at level 40, f at level 50). *) *)

(* Section MonadInstances. *)

(*   Definition Id (A : Type) := A. *)

(*   Definition id_ret A (x : A) : Id A := *)
(*     x. *)

(*   Definition id_bind A B (a : Id A) (f : A -> Id B) : Id B := f a. *)

(*   Lemma id_left_identity : *)
(*     forall A B (a : A) (f : A -> Id B), *)
(*       id_bind (id_ret a) f = f a. *)
(*   Proof. *)
(*     repeat intro. *)
(*     unfold id_ret. *)
(*     unfold id_bind. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Lemma id_right_identity : *)
(*     forall A (ia : Id A), *)
(*       id_bind ia (fun a => id_ret a) = ia. *)
(*   Proof. *)
(*     repeat intro. *)
(*     unfold id_bind. *)
(*     unfold id_ret. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Lemma id_associativity : *)
(*     forall A B C (ia : Id A) (f : A -> Id B) (g : B -> Id C), *)
(*       id_bind ia (fun a => id_bind (f a) g) = id_bind (id_bind ia f) g. *)
(*   Proof. *)
(*     repeat intro. *)
(*     unfold id_bind. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Global Instance id_monad : Monad Id := *)
(*     { *)
(*       ret := id_ret; *)
(*       bind := id_bind; *)
(*       left_unit := id_left_identity; *)
(*       right_unit := id_right_identity; *)
(*       bind_assoc := id_associativity *)
(*     }. *)

(*   Inductive Maybe A := *)
(*   | nothing : Maybe A *)
(*   | just : A -> Maybe A. *)

(*   Global Arguments nothing {_}. *)

(*   Definition maybe_ret A (a : A) : Maybe A := *)
(*     just a. *)

(*   Definition maybe_bind A B (ma : Maybe A) (f : A -> Maybe B) : Maybe B := *)
(*     match ma with *)
(*     | nothing => nothing *)
(*     | just a => f a *)
(*     end. *)

(*   Lemma maybe_left_identity : *)
(*     forall A B (a : A) (f : A -> Maybe B), *)
(*       maybe_bind (maybe_ret a) f = f a. *)
(*   Proof. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Lemma maybe_right_identity : *)
(*     forall A (ma : Maybe A), *)
(*       maybe_bind ma (@maybe_ret A) = ma. *)
(*   Proof. *)
(*     induction ma. *)
(*     - reflexivity. *)
(*     - reflexivity. *)
(*   Qed. *)

(*   Lemma maybe_associativity : *)
(*     forall A B C (ma : Maybe A) (f : A -> Maybe B) (g : B -> Maybe C), *)
(*       maybe_bind ma (fun a => maybe_bind (f a) g) = maybe_bind (maybe_bind ma f) g. *)
(*   Proof. *)
(*     intros. *)
(*     induction ma. *)
(*     - reflexivity. *)
(*     - reflexivity. *)
(*   Qed. *)

(*   Global Instance maybe_monad : Monad Maybe := *)
(*     { *)
(*       ret := maybe_ret; *)
(*       bind := maybe_bind; *)
(*       left_unit := maybe_left_identity; *)
(*       right_unit := maybe_right_identity; *)
(*       bind_assoc := maybe_associativity *)
(*     }. *)

(* End MonadInstances. *)

(* Section FunctorClass. *)

(*   Class Functor (F: Type -> Type) := *)
(*     { *)
(*       fmap : forall A B, (A -> B) -> F A -> F B; *)
(*       fmap_id : forall A (fx : F A), fmap (fun x => x) fx = fx; *)
(*       fmap_comp : forall A B C (f : B -> C) (g : A -> B) (fx : F A), *)
(*           fmap f (fmap g fx) = fmap (fun x => f (g x)) fx *)
(*     }. *)

(* End FunctorClass. *)
