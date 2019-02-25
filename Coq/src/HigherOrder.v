Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Thesis.Base.
Require Import Thesis.Search.

Inductive Ext Shape (Pos : Shape -> Type) A := ext : forall s, (Pos s -> A) -> Ext Shape Pos A.


Arguments ext {_} {_} {_} s pf.
Set Implicit Arguments.

Class HContainer (H : (Type -> Type) -> Type -> Type) (M : Type -> Type) :=
  {
    Shape   : Type;
    Pos     : Shape -> Type;
    to      : forall A, Ext Shape Pos (M A) -> H M A;
    from    : forall A, H M A -> Ext Shape Pos (M A);
    to_from : forall A (fx : H M A), @to A (@from A fx) = fx;
    from_to : forall A (e : Ext Shape Pos (M A)), @from A (@to A e) = e
  }.

Arguments from {_} {_} {_} _.

Section Free.
  Variable H : (Type -> Type) -> Type -> Type.
  Variable M : (Type -> Type).

  Inductive Free (HC__F : HContainer H M) A :=
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

  Instance C__Zero M : HContainer Zero M :=
    {
      Shape := Shape__Zero;
      Pos   := Pos__Zero;
      to    := @to__Zero M;
      from  := @from__Zero M;
      to_from := @to_from__Zero M;
      from_to := @from_to__Zero M
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
      
  Instance C__Choice M : HContainer Choice M :=
    {
      Shape := Shape__Choice;
      Pos   := Pos__Choice;
      to    := @to__Choice M;
      from  := @from__Choice M;
      to_from := @to_from__Choice M;
      from_to := @from_to__Choice M
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

  Instance C__State M : HContainer State M :=
    {
      Shape := Shape__State;
      Pos   := Pos__State;
      to    := @to__State M;
      from  := @from__State M;
      to_from := @to_from__State M;
      from_to := @from_to__State M
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
    | csharing _ _ n mx xma =>
      ext (ssharing M _ n mx)
          (fun p : Pos__Sharing (ssharing M _ n mx) =>
             (match p in Pos__Sharing (ssharing _ X n mx) return (X -> M A) -> M A with
                psharing _ x m mx' => fun f => f x
              end) xma)
    end.

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
     
  Instance C__Sharing (M : Type -> Type) : HContainer Sharing M :=
    {
      Shape := Shape__Sharing M;
      Pos   := @Pos__Sharing M;
      to    := @to__Sharing M;
      from  := @from__Sharing M;
      to_from := @to_from__Sharing M;
      from_to := @from_to__Sharing M
    }.
End Sharing.

Inductive ChoiceF A :=
| c_fail : ChoiceF A
| c_choice : A -> A -> ChoiceF A.

Definition Prog M := Free (C__Choice M).
Definition NDShare := C__Choice.
Definition Fail M A : Prog M A :=
  let s := sfail
    in @impure Choice M (C__Choice M) A (ext s (fun p : Pos__Choice s => match p with end)).

Arguments Fail {_}.

Definition Choice' M A mid (l r : Prog M A) : Prog M A :=
  let s := schoice mid
  in @impure Choice M (C__Choice M) A (ext s (fun p : Pos__Choice s => if p then l else r)).

Fixpoint runChoice M A (fc : Free (C__Choice M) A) : Tree A :=
  match fc with
  | pure _ x => Leaf x
  | impure (ext sfail   _)  => Empty A
  | impure (ext (schoice mid) pf) => Branch mid (runChoice (pf true)) (runChoice (pf false))
  end.

Require Import Lists.List.
Import ListNotations.

Definition handle M A (p : Prog M A) := collectVals (runChoice p).
Definition coin M := @Choice' M bool None (pure _ true) (pure _ false).
Example example1 := coin.
Example res_example1 := [true; false].

Example example2 M := Choice' None (coin M)  (coin M).
Example res_example2 := [true; false; true; false].

Definition exBs := [(example1, res_example1); (example2, res_example2)].
  
Lemma tests__exBs : forall M, Forall (fun '(p,r) => handle (p M) = r) exBs.
Proof. repeat econstructor. Qed.

Definition Share' (n : nat) M A (fs : Free (C__Sharing M) A) : Free (C__Sharing M) A.
  apply impure.
  eapply ext.
  intros.
  apply fs.
  Unshelve.
  simpl.
  eapply ssharing.
  - apply n.
  - Admitted.
