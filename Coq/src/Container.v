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

End Zero.

Section Combination.

  Variable F G : Type -> Type.
  Variable C1 : Container F.
  Variable C2 : Container G.

  Inductive Comb A : Type :=
  | Inl : F A -> Comb A
  | Inr : G A -> Comb A.

  Definition fold_sum (A B : Type) (C : sum A B -> Type)
           (f : forall (a : A), C (inl _ a))
           (g : forall (b : B), C (inr _ b))
           (x : A + B) : C x :=
  match x with
  | inl y => f y
  | inr y => g y
  end.

  Definition fold_sum' (A B : Type) (C : Type) (f : A -> C) (g : B -> C) (x : A + B) : C :=
    fold_sum (fun _ => C) f g x.

  Definition Shape__Comb : Type := sum (@Shape F C1) (@Shape G C2).
  Definition Pos__Comb : Shape__Comb -> Type := fold_sum' (@Pos F C1) (@Pos G C2).

  Definition Ext__Comb A := Ext Shape__Comb Pos__Comb A.

  Definition to__Comb (A : Type) (e: Ext__Comb A) : Comb A :=
    match e with
    | ext (inl s1) pf => Inl (to (ext s1 pf))
    | ext (inr s2) pf => Inr (to (ext s2 pf))
    end.

  Fixpoint from__Comb A (z : Comb A) : Ext__Comb A :=
    match z with
    | Inl fa => match from fa with
                 ext s1 pf1 => ext (inl s1) pf1
               end
    | Inr ga => match from ga with
                 ext s2 pf2 => ext (inr s2) pf2
               end
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

Section Choice.

  Inductive Choice (A : Type) :=
  | cfail   : Choice A
  | cchoice : option (nat * nat) -> A -> A -> Choice A.

  Inductive Shape__Choice :=
  | sfail : Shape__Choice
  | schoice : option (nat * nat) -> Shape__Choice.

  Definition Pos__Choice (s: Shape__Choice) : Type :=
    match s with
    | sfail  => Void
    | schoice _ => bool
    end.

  Definition Ext__Choice A := Ext Shape__Choice Pos__Choice A.

  Definition to__Choice A (e: Ext__Choice A) : Choice A :=
    match e with
    | ext sfail f   => cfail A
    | ext (schoice mid) f => cchoice mid (f true) (f false)
    end.

  Fixpoint from__Choice A (z : Choice A) : Ext__Choice A :=
    match z with
    | cfail _     => ext sfail   (fun p : Pos__Choice sfail => match p with end)
    | cchoice mid l r => ext (schoice mid) (fun p : Pos__Choice (schoice mid) => if p then l else r)
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

End State.

Section Sharing.

  Inductive Sharing (A : Type) :=
  | csharing : nat -> A -> Sharing A.

  Inductive Shape__Sharing :=
  | ssharing : nat -> Shape__Sharing.

  Inductive Pos__Sharing : Shape__Sharing -> Type :=
  | psharing : forall (n : nat), Pos__Sharing (ssharing n).

  Definition Ext__Sharing A := Ext Shape__Sharing Pos__Sharing A.

  Definition to__Sharing A (e: Ext__Sharing A) : Sharing A :=
    match e with
    | ext (ssharing n) fp => csharing n (fp (psharing n))
    end.

  Fixpoint from__Sharing A (z : Sharing A) : Ext__Sharing A :=
    match z with
    | csharing n a => ext (ssharing n) (fun p : Pos__Sharing (ssharing n) => match p with psharing _ => a end)
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
      (simpl;
       f_equal;
       apply functional_extensionality;
       intros p;
       dependent destruction p;
       reflexivity).
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

