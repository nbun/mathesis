Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Thesis.Base.
Require Import Thesis.Search.

Inductive Ext Shape (Pos : Shape -> Type) A := ext : forall s, (Pos s -> A) -> Ext Shape Pos A.

Arguments ext {_} {_} {_} s pf.
Set Implicit Arguments.

Class HContainer (H : (Type -> Type) -> Type -> Type) :=
  {
    Shape   : Type;
    Pos     : Shape -> Type;
    to      : forall M A, Ext Shape Pos (M A) -> H M A;
    from    : forall M A, H M A -> Ext Shape Pos (M A);
    to_from : forall M A (fx : H M A), @to M A (@from M A fx) = fx;
    from_to : forall M A (e : Ext Shape Pos (M A)), @from M A (@to M A e) = e
  }.

Class HContainer2 (H : (Type -> Type) -> Type -> Type) (M : Type -> Type) :=
  {
    Shape2   : Type;
    Pos2     : Shape2 -> Type;
    to2      : forall A, Ext Shape2 Pos2 (M A) -> H M A;
    from2    : forall A, H M A -> Ext Shape2 Pos2 (M A);
    to_from2 : forall A (fx : H M A), @to2 A (@from2 A fx) = fx;
    from_to2 : forall A (e : Ext Shape2 Pos2 (M A)), @from2 A (@to2 A e) = e
  }.

Arguments from {_} {_} {_} _.

Section Free.
  Variable H : (Type -> Type) -> Type -> Type.

  Inductive Free (HC__F : HContainer H) A :=
  | pure : A -> Free HC__F A
  | impure : Ext Shape Pos (Free HC__F A) -> Free HC__F A.

End Free.
Arguments pure {_} {_} {_} _.

Section Zero.

  Inductive Void :=.

  Definition Zero (M : Type -> Type) (A : Type) := Void.

  Definition Shape__Zero := Void.

  Definition Pos__Zero (s: Shape__Zero) := Void.

  Definition Ext__Zero A := Ext Shape__Zero Pos__Zero A.

  Definition to__Zero M A (e: Ext__Zero (M A)) : Zero M A :=
    match e with
      ext s _ => match s with end
    end.

  Definition from__Zero M A (z: Zero M A) : Ext__Zero (M A) :=
    match z with end.

  Lemma to_from__Zero : forall M A (ox : Zero M A), to__Zero M A (from__Zero ox) = ox.
  Proof.
    intros M A ox.
    destruct ox.
  Qed.

  Lemma from_to__Zero : forall M A (e : Ext__Zero (M A)), from__Zero (to__Zero M A e) = e.
  Proof.
    intros M A [s pf].
    destruct s.
  Qed.

  Instance C__Zero : HContainer Zero :=
    {
      Shape := Shape__Zero;
      Pos   := Pos__Zero;
      to    := to__Zero;
      from  := from__Zero;
      to_from := to_from__Zero;
      from_to := from_to__Zero
    }.

End Zero.

Section Choice.

  Inductive Choice M (A : Type) :=
  | cfail   : Choice M A
  | cchoice : option (nat * nat) -> M A -> M A -> Choice M A.

  Inductive Shape__Choice :=
  | sfail : Shape__Choice
  | schoice : option (nat * nat) -> Shape__Choice.

  Definition Pos__Choice (s: Shape__Choice) : Type :=
    match s with
    | sfail  => Void
    | schoice _ => bool
    end.

  Definition Ext__Choice A := Ext Shape__Choice Pos__Choice A.

  Definition to__Choice M A (e: Ext__Choice (M A)) : Choice M A :=
    match e with
    | ext sfail f   => cfail M A
    | ext (schoice mid) f => cchoice M A mid (f true) (f false)
    end.

  Fixpoint from__Choice M A (z : Choice M A) : Ext__Choice (M A) :=
    match z with
    | cfail _ _     => ext sfail   (fun p : Pos__Choice sfail => match p with end)
    | cchoice _ _ mid l r => ext (schoice mid) (fun p : Pos__Choice (schoice mid) => if p then l else r)
    end.

  Lemma to_from__Choice : forall M A (ox : Choice M A), to__Choice M A (from__Choice ox) = ox.
  Proof.
    intros M A ox.
    destruct ox; reflexivity.
  Qed.

  Lemma from_to__Choice : forall M A (e : Ext__Choice (M A)), from__Choice (to__Choice M A e) = e.
  Proof.
    intros M A [s pf].
    destruct s; simpl; f_equal; apply functional_extensionality; intros x.
    - contradiction.
    - destruct x; reflexivity.
  Qed.
      
  Instance C__Choice : HContainer Choice :=
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

  Inductive State M (A : Type) :=
  | get : (S -> M A) -> State M A
  | put : S -> M A -> State M A.

  Inductive Shape__State :=
  | sget : Shape__State
  | sput : S -> Shape__State.
  
  Inductive Pos__State : Shape__State -> Type :=
  | pget : forall (st : S), Pos__State sget
  | pput : forall (st : S), Pos__State (sput st).

  Definition Ext__State A := Ext Shape__State Pos__State A.

  Definition to__State M A (e: Ext__State (M A)) : State M A :=
    match e with
    | ext sget     fp => get M A (fun s => fp (pget s))
    | ext (sput s) fp => put M A s (fp (pput s))
    end.

  Fixpoint from__State M A (z : State M A) : Ext__State (M A) :=
    match z with
    | get _ _ f   => ext sget     (fun p : Pos__State sget => match p with pget s => f s end)
    | put _ _ s a => ext (sput s) (fun p : Pos__State (sput s) => a)
    end.

  Lemma to_from__State : forall M A (ox : State M A), to__State M A (from__State ox) = ox.
  Proof.
    intros M A ox.
    destruct ox.
    - simpl. f_equal.
    - reflexivity.
  Qed.

  Lemma from_to__State : forall M A (e : Ext__State (M A)), from__State (to__State M A e) = e.
  Proof.
    intros M A [s pf].
    destruct s;
      (simpl;
       f_equal;
       apply functional_extensionality;
       intros p;
       dependent destruction p;
       reflexivity).
  Qed.

  Instance C__State : HContainer State :=
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

  Inductive Sharing M (A : Type) :=
  | csharing : forall X, nat -> M X -> (X -> M A) -> Sharing M A.

  Inductive Shape__Sharing (M : Type -> Type) :=
  | ssharing : forall X, nat -> M X -> Shape__Sharing M.

  Inductive Pos__Sharing M : Shape__Sharing M -> Type :=
  | psharing : forall X (x : X) (n : nat) (mx : M X), Pos__Sharing (ssharing M X n mx).

  Definition Ext__Sharing A := forall (M : Type -> Type), Ext (Shape__Sharing M) (@Pos__Sharing M) A.

  Definition to__Sharing M A (e: Ext (Shape__Sharing M) (@Pos__Sharing M) (M A)) : Sharing M A :=
    match e with
    | ext (ssharing _ _ n mx) fp => csharing M A n mx (fun x => fp (psharing M x n mx))
    end.

  Definition from__Sharing M A (z : Sharing M A) : Ext (Shape__Sharing M) (@Pos__Sharing M) (M A) :=
    match z with
    | csharing _ _ n mx xma => ext (ssharing M _ n mx)
                                  (fun p : Pos__Sharing (ssharing M _ n mx) =>
                                     (match p in Pos__Sharing (ssharing _ X n mx) return (X -> M A) -> M A with
                                       psharing _ x m mx' => fun f => f x
                                     end) xma)
    end.

  (*   destruct z as [X n mx xma]. *)
  (*   apply ext with (s := ssharing M _ n mx). *)
  (*   intro p. *)
  (*   dependent destruction p. *)
  (*   apply xma. *)
  (*   apply x. *)
  (* Defined. *)

  Lemma to_from__Sharing : forall M A (ox : Sharing M A), to__Sharing A (from__Sharing ox) = ox.
  Proof.
    intros M A ox.
    destruct ox; reflexivity.
  Qed.

  Lemma from_to__Sharing : forall M A (e : Ext (Shape__Sharing M) (@Pos__Sharing M) (M A)), from__Sharing (to__Sharing _ e) = e.
  Proof.
    intros M A [s pf].
    destruct s;
      (simpl;
       f_equal;
       apply functional_extensionality;
       intros p;
       dependent destruction p;
       reflexivity).
  Qed.
     
  Instance C__Sharing (M : Type -> Type) : HContainer2 Sharing M :=
    {
      Shape2 := Shape__Sharing M;
      Pos2   := @Pos__Sharing M;
      to2    := @to__Sharing M;
      from2  := @from__Sharing M;
      to_from2 := @to_from__Sharing M;
      from_to2 := @from_to__Sharing M
    }.
End Sharing.

Definition Prog := Free C__Choice.
Definition NDShare := C__Choice.
Definition Fail A : Prog A :=
  let s : @Shape _ NDShare := sfail
    in impure (ext s (fun p : @Pos _ NDShare s => match p with end)).

Arguments Fail {_}.

Definition Choice' A mid l r : Prog A :=
  let s : @Shape _ NDShare := schoice mid
  in impure (ext s (fun p : @Pos _ NDShare s => if p then l else r)).

Fixpoint runChoice A (fc : Free C__Choice A) : Tree A :=
  match fc with
  | pure x => Leaf x
  | impure (ext sfail   _)  => Empty A
  | impure (ext (schoice mid) pf) => Branch (Some (42, 42, 42)) (runChoice (pf true)) (runChoice (pf false))
  end.

Require Import Lists.List.
Import ListNotations.

Definition handle A (p : Prog A) := collectVals (runChoice p).
Definition coin := Choice' None (pure true) (pure false).
Example example1 : Prog bool := coin.
Example res_example1 := [true; false].

Example example2 : Prog bool := Choice' None coin  coin.
Example res_example2 := [true; false; true; false].

Definition exBs := [(example1, res_example1); (example2, res_example2)].
  
Lemma tests__exBs : Forall (fun '(p,r) => handle p = r) exBs.
Proof. repeat econstructor. Qed.
