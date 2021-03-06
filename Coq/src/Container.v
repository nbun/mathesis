(** Definition of the container class and effect containers *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

(** Extension of a container *)
Inductive Ext Shape (Pos : Shape -> Type) A := ext : forall s, (Pos s -> A) -> Ext Shape Pos A.

Arguments ext {_} {_} {_} s pf.
Set Implicit Arguments.

(** Container class with transformation functions and isomorphism properties *)
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

(** Zero corresponds to the Void effect in Haskell *)
Section Zero.

  Inductive Void :=.

  (** Original data type *)
  Definition Zero (A : Type) := Void.

  Definition Shape__Zero := Void.

  Definition Pos__Zero (s: Shape__Zero) := Void.

  (** Container extension for Zero *)
  Definition Ext__Zero A := Ext Shape__Zero Pos__Zero A.

  (** Transformation functions *)
  Definition to__Zero A (e: Ext__Zero A) : Zero A :=
    match e with
      ext s _ => match s with end
    end.

  Definition from__Zero A (z: Zero A) : Ext__Zero A :=
    match z with end.

  (** Isomorphism proofs *)
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

  (** Container instance *)
  Instance C__Zero : Container Zero :=
    {
      Shape := Shape__Zero;
      Pos   := Pos__Zero;
      to    := to__Zero;
      from  := from__Zero;
      to_from := to_from__Zero;
      from_to := from_to__Zero
    }.

End Zero.

(** The comb container represents the :+: functor for combining effects *)
Section Combination.

  Variable F G : Type -> Type.
  Variable C__F : Container F.
  Variable C__G : Container G.

  Inductive Comb A : Type :=
  | Inl : F A -> Comb A
  | Inr : G A -> Comb A.

  Definition Shape__Comb : Type := sum (@Shape F C__F) (@Shape G C__G).

  Definition Pos__Comb (s : Shape__Comb) : Type :=
    match s with
    | inl x => @Pos F C__F x
    | inr x => @Pos G C__G x
    end.

  Definition Ext__Comb A := Ext Shape__Comb Pos__Comb A.

  Definition to__Comb (A : Type) (e: Ext__Comb A) : Comb A :=
    match e with
    | ext (inl s) pf => Inl (to (ext s pf))
    | ext (inr s) pf => Inr (to (ext s pf))
    end.

  Definition from__Comb A (z : Comb A) : Ext__Comb A :=
    match z with
    | Inl x => let '(ext s pf) := from x in ext (inl s) pf
    | Inr x => let '(ext s pf) := from x in ext (inr s) pf
    end.

  Lemma to_from__Comb : forall A (ox : Comb A), to__Comb (from__Comb ox) = ox.
  Proof.
    intros A ox.
    destruct ox as [f|f];
      (simpl;
       destruct (from f) eqn:H;
       unfold to__Comb;
       rewrite <- H;
       rewrite to_from;
       reflexivity).
  Qed.

  Lemma from_to__Comb : forall A (e : Ext__Comb A), from__Comb (to__Comb e) = e.
  Proof.
    intros A [s pf].
    destruct s; (simpl; rewrite from_to; reflexivity).
  Qed.

  Instance C__Comb : Container Comb :=
    {
      Shape := Shape__Comb;
      Pos   := Pos__Comb;
      to    := to__Comb;
      from  := from__Comb;
      to_from := to_from__Comb;
      from_to := from_to__Comb
    }.

End Combination.

(** Non-determinism effect container *)
Section Choice.
  Definition ID : Type := (nat * nat * nat).

  Inductive Choice (A : Type) :=
  | cfail   : Choice A
  | cchoice : option ID -> A -> A -> Choice A.

  Inductive Shape__Choice :=
  | sfail : Shape__Choice
  | schoice : option ID -> Shape__Choice.

  Definition Pos__Choice (s: Shape__Choice) : Type :=
    match s with
    | sfail  => Void
    | schoice _ => bool
    end.

  Definition Ext__Choice : Type -> Type := Ext Shape__Choice Pos__Choice.

  Definition to__Choice A (e: Ext__Choice A) : Choice A :=
    match e with
    | ext sfail f   => cfail A
    | ext (schoice mid) f => cchoice mid (f true) (f false)
    end.

  Definition from__Choice A (z : Choice A) : Ext__Choice A :=
    match z with
    | cfail _     =>
      ext sfail (fun p : Pos__Choice sfail => match p with end)
    | cchoice mid l r =>
      let s := schoice mid
      in ext s (fun p : Pos__Choice s => if p then l else r)
    end.

  Lemma to_from__Choice : forall A (ox : Choice A), to__Choice (from__Choice ox) = ox.
  Proof.
    intros A ox.
    destruct ox; reflexivity.
  Qed.

  Lemma from_to__Choice : forall A (e : Ext__Choice A), from__Choice (to__Choice e) = e.
  Proof.
    intros A [s pf].
    destruct s; simpl; f_equal; extensionality p.
    - contradiction.
    - destruct p; reflexivity.
  Qed.
      
  Instance C__Choice : Container Choice :=
    {
      to_from := to_from__Choice;
      from_to := from_to__Choice
    }.

End Choice.

(** State effect container *)
Section State.

  Variable S : Type.

  Inductive State (A : Type) :=
  | get : (S -> A) -> State A
  | put : S -> A -> State A.

  Inductive Shape__State :=
  | sget : Shape__State
  | sput : S -> Shape__State.

  Definition Pos__State (s : Shape__State) : Type :=
    match s with
    | sget   => S
    | sput _ => unit
    end.
  
  Definition Ext__State A := Ext Shape__State Pos__State A.

  Definition to__State (A : Type) (e: Ext__State A) : State A :=
    match e with
    | ext sget     fp => get (fun s => fp s)
    | ext (sput s) fp => put s (fp tt)
    end.
  
  Definition from__State A (z : State A) : Ext__State A :=
    match z with
    | get f   => ext sget     (fun p : Pos__State sget => f p)
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

End State.

Arguments sget {_}.

(** Sharing effect container *)
Section Sharing.

  Inductive Sharing (A : Type) :=
  | cbsharing : (nat * nat) -> A -> Sharing A
  | cesharing : (nat * nat) -> A -> Sharing A.

  Inductive Shape__Sharing :=
  | sbsharing : (nat * nat) -> Shape__Sharing
  | sesharing : (nat * nat) -> Shape__Sharing.

  Definition Pos__Sharing : Shape__Sharing -> Type := fun _ => unit.

  Definition Ext__Sharing := Ext Shape__Sharing Pos__Sharing.

  Definition to__Sharing A (e: Ext__Sharing A) : Sharing A :=
    match e with
    | ext (sbsharing n) fp => cbsharing n (fp tt)
    | ext (sesharing n) fp => cesharing n (fp tt)
    end.

  Definition from__Sharing A (z : Sharing A) : Ext__Sharing A :=
    match z with
    | cbsharing n a => ext (sbsharing n) (fun _ => a)
    | cesharing n a => ext (sesharing n) (fun _ => a)
    end.

  Lemma to_from__Sharing : forall A (ox : Sharing A), to__Sharing (from__Sharing ox) = ox.
  Proof.
    intros A ox.
    destruct ox; reflexivity.
  Qed.

  Lemma from_to__Sharing : forall A (e : Ext__Sharing A), from__Sharing (to__Sharing e) = e.
  Proof.
    intros A [s pf].
    destruct s;
      simpl;
      f_equal;
      extensionality p';
      destruct p';
      reflexivity.
  Qed.
     
  Instance C__Sharing : Container Sharing :=
    {
      Shape := Shape__Sharing;
      Pos   := Pos__Sharing;
      to    := to__Sharing;
      from  := from__Sharing;
      to_from := to_from__Sharing;
      from_to := from_to__Sharing
    }.

End Sharing.
