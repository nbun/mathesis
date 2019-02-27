Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Thesis.Base.
Require Import Thesis.Search.

Inductive Ext Shape (Pos : Shape -> Type) (Ctx : forall s : Shape, Pos s -> Type -> Type) (F : Type -> Type) A :=
  ext : forall s, (forall p : Pos s, F (Ctx s p A)) -> Ext Shape Pos Ctx F A.

Arguments ext {_ _ _ _ _} s pf.

Set Implicit Arguments.

Class HContainer (H : (Type -> Type) -> Type -> Type) :=
  {
    Shape   : Type;
    Pos     : Shape -> Type;
    Ctx     : forall s : Shape, Pos s -> Type -> Type;
    to      : forall F A, Ext Shape Pos Ctx F A -> H F A;
    from    : forall F A, H F A -> Ext Shape Pos Ctx F A;
    to_from : forall F A (fx : H F A), to (from fx) = fx;
    from_to : forall F A (e : Ext Shape Pos Ctx F A), from (to e) = e
  }.

Arguments from {_ _ _} _.

Section Free.

  Variable H : (Type -> Type) -> Type -> Type.

  Inductive Free (C : HContainer H) A :=
  | pure : A -> Free C A
  | impure : Ext Shape Pos Ctx (Free C) A -> Free C A.

End Free.

Arguments pure {_} {_} {_} _.

Section Zero.

  Inductive Void :=.

  Definition Zero (M : Type -> Type) (A : Type) := Void.

  Definition Shape__Zero := Void.

  Definition Pos__Zero (s : Shape__Zero) := Void.

  Definition Ctx__Zero (s : Shape__Zero) : Pos__Zero s -> Type -> Type := match s with end.

  Definition Ext__Zero := Ext Shape__Zero Pos__Zero Ctx__Zero.

  Definition to__Zero F A (e: Ext__Zero F A) : Zero F A :=
    match e with
      ext s _ => match s with end
    end.

  Definition from__Zero F A (z: Zero F A) : Ext__Zero F A :=
    match z with end.

  Lemma to_from__Zero : forall F A (ox : Zero F A), to__Zero (from__Zero ox) = ox.
  Proof.
    intros F A ox.
    destruct ox.
  Qed.

  Lemma from_to__Zero : forall F A (e : Ext__Zero F A), from__Zero (to__Zero e) = e.
  Proof.
    intros F A [s pf].
    destruct s.
  Qed.

  Instance C__Zero : HContainer Zero :=
    {
      Shape := Shape__Zero;
      Pos   := Pos__Zero;
      Ctx   := Ctx__Zero;
      to    := to__Zero;
      from  := from__Zero;
      to_from := to_from__Zero;
      from_to := from_to__Zero
    }.

End Zero.

Section Choice.

  Inductive Choice M (A : Type) :=
  | cfail   : Choice M A
  | cchoice : option (nat * nat * nat) -> M A -> M A -> Choice M A.

  Inductive Shape__Choice :=
  | sfail : Shape__Choice
  | schoice : option (nat * nat * nat) -> Shape__Choice.

  Definition Pos__Choice (s: Shape__Choice) : Type :=
    match s with
    | sfail  => Void
    | schoice _ => bool
    end.

  Definition Ctx__Choice (s : Shape__Choice) : Pos__Choice s -> Type -> Type :=
    match s with
    | sfail     => fun _ A => A
    | schoice _ => fun _ A => A
    end.

  Definition Ext__Choice := Ext Shape__Choice Pos__Choice Ctx__Choice.

  Definition to__Choice F A (e: Ext__Choice F A) : Choice F A :=
    match e with
    | ext sfail f   => cfail F A
    | ext (schoice mid) f => cchoice F A mid (f true) (f false)
    end.

  Fixpoint from__Choice F A (z : Choice F A) : Ext__Choice F A :=
    match z with
    | cfail _ _     => ext sfail   (fun p : Pos__Choice sfail => match p with end)
    | cchoice _ _ mid l r => ext (schoice mid) (fun p : Pos__Choice (schoice mid) => if p then l else r)
    end.

  Lemma to_from__Choice : forall F A (ox : Choice F A), to__Choice (from__Choice ox) = ox.
  Proof.
    intros F A ox.
    destruct ox; reflexivity.
  Qed.

  Lemma from_to__Choice : forall F A (e : Ext__Choice F A), from__Choice (to__Choice e) = e.
  Proof.
    intros F A [s pf].
    destruct s; simpl; f_equal; extensionality p.
    - contradiction.
    - destruct p; reflexivity.
  Qed.
      
  Instance C__Choice : HContainer Choice :=
    {
      Shape := Shape__Choice;
      Pos   := Pos__Choice;
      Ctx   := Ctx__Choice;
      to    := to__Choice;
      from  := from__Choice;
      to_from := to_from__Choice;
      from_to := from_to__Choice
    }.
End Choice.

Section State.

  Variable S : Type.

  Inductive State M (A : Type) :=
  | get : (S -> M A) -> State M A
  | put : S -> M A -> State M A.

  Inductive Shape__State :=
  | sget : Shape__State
  | sput : S -> Shape__State.
  
  Inductive Pos__State : Shape__State -> Type :=
  | pget : forall (st : S), Pos__State sget
  | pput : forall (st : S), Pos__State (sput st).

  Definition Ctx__State (s : Shape__State) : Pos__State s -> Type -> Type :=
    match s with
    | sget   => fun _ A => A
    | sput _ => fun _ A => A
    end.

  Definition Ext__State := Ext Shape__State Pos__State Ctx__State.

  Definition to__State F A (e: Ext__State F A) : State F A :=
    match e with
    | ext sget     fp => get F A (fun s => fp (pget s))
    | ext (sput s) fp => put F A s (fp (pput s))
    end.

  Fixpoint from__State F A (z : State F A) : Ext__State F A :=
    match z with
    | get _ _ f   => ext sget     (fun p : Pos__State sget => match p with pget s => f s end)
    | put _ _ s a => ext (sput s) (fun p : Pos__State (sput s) => a)
    end.

  Lemma to_from__State : forall F A (ox : State F A), to__State (from__State ox) = ox.
  Proof.
    intros F A ox.
    destruct ox.
    - simpl. f_equal.
    - reflexivity.
  Qed.

  Lemma from_to__State : forall F A (e : Ext__State F A), from__State (to__State e) = e.
  Proof.
    intros F A [s pf].
    destruct s;
      (simpl;
       f_equal;
       extensionality p;
       dependent destruction p;
       reflexivity).
  Qed.

  Instance C__State : HContainer State :=
    {
      Shape := Shape__State;
      Pos   := Pos__State;
      Ctx   := Ctx__State;
      to    := to__State;
      from  := from__State; 
      to_from := to_from__State;
      from_to := from_to__State
    }.

End State.

Section Sharing.

  Inductive Sharing F (A : Type) :=
  | csharing : forall X, nat * nat -> F X -> (X -> F A) -> Sharing F A.

  Inductive Shape__Sharing :=
  | ssharing : nat * nat -> Type -> Shape__Sharing.

  Definition shapeType (s : Shape__Sharing) : Type :=
    let '(ssharing _ X) := s in X.

  Inductive Pos__Sharing (s : Shape__Sharing) : Type :=
  | pshared : Pos__Sharing s
  | pcont   : shapeType s -> Pos__Sharing s.

  Definition Ctx__Sharing (s : Shape__Sharing) (p : Pos__Sharing s) : Type -> Type :=
    match p with
    | pshared _ => fun _ => shapeType s
    | pcont _ _ => fun A => A
    end.

  Definition Ext__Sharing := Ext Shape__Sharing Pos__Sharing Ctx__Sharing.

  Definition to__Sharing F A (e: Ext__Sharing F A) : Sharing F A :=
    match e with
    | ext (ssharing n _ as s) fp => csharing F A n (fp (pshared s)) (fun x => fp (pcont s x))
    end.

  Definition from__Sharing F A (z : Sharing F A) : Ext__Sharing F A :=
    match z with
    | csharing _ _ n fx xfa => ext (ssharing n _)
                                  (fun p : Pos__Sharing (ssharing n _) =>
                                     match p with
                                     | pshared _ => fx
                                     | pcont _ s => xfa s
                                     end)
    end.

  Lemma to_from__Sharing : forall F A (ox : Sharing F A), to__Sharing (from__Sharing ox) = ox.
  Proof.
    intros F A ox.
    destruct ox; reflexivity.
  Qed.

  Lemma from_to__Sharing : forall F A (e : Ext__Sharing F A), from__Sharing (to__Sharing e) = e.
  Proof.
    intros F A [s pf].
    destruct s;
      simpl;
      f_equal;
      extensionality pos;
      dependent destruction pos;
      reflexivity.
  Qed.
     
  Instance C__Sharing : HContainer Sharing :=
    {
      Shape := Shape__Sharing;
      Pos   := Pos__Sharing;
      Ctx   := Ctx__Sharing;
      to    := to__Sharing;
      from  := from__Sharing;
      to_from := to_from__Sharing;
      from_to := from_to__Sharing
    }.
End Sharing.

Definition Fail A : Free C__Choice A.
  apply impure.
  apply ext with (s := sfail).
  intros.
  destruct p.
Defined.

Arguments Fail {_}.

Definition Choice' A (mid : option (nat * nat * nat)) (p q : Free C__Choice A) : Free C__Choice A.
  apply impure.
  apply ext with (s := schoice mid).
  intros.
  destruct p0.
  - apply p.
  - apply q.
Defined.

Fixpoint runChoice A (fc : Free C__Choice A) : Tree A :=
  match fc with
  | pure x => Leaf x
  | impure (ext sfail   _)  => Empty A
  | impure (ext (schoice mid) pf) => Branch mid (runChoice (pf true)) (runChoice (pf false))
  end.

Require Import Lists.List.
Import ListNotations.

Definition handle A (p : Free C__Choice A) := collectVals (runChoice p).
Definition coin  := Choice' None (pure true) (pure false).
Example example1 := coin.
Example res_example1 := [true; false].

Example example2 := Choice' None coin coin.
Example res_example2 := [true; false; true; false].

Definition exBs := [(example1, res_example1); (example2, res_example2)].
  
Lemma tests__exBs : Forall (fun '(p,r) => handle p = r) exBs.
Proof. repeat econstructor. Qed.

Definition Share' (n : nat * nat) A (fs : Free C__Sharing A) : Free C__Sharing A.
  apply impure.
  apply ext with (s := ssharing n A).
  intros.
  destruct p.
  - apply fs.
  - simpl.
    apply pure.
    apply s.
Defined.