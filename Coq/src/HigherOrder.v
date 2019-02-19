Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Thesis.Base.
Require Import Thesis.Search.

Inductive Ext Shape (Pos : Shape -> Type) (M : Type -> Type) A := ext : forall s, (Pos s -> A) -> Ext Shape Pos M A.

Arguments ext {_} {_} {_} {_} s pf.
Set Implicit Arguments.

Class HContainer (H : (Type -> Type) -> Type -> Type) :=
  {
    Shape   : forall M, Type;
    Pos     : forall M, Shape M -> Type;
    to      : forall M A, Ext (Shape M) (@Pos M) M (M A) -> H M A;
    from    : forall M A, H M A -> Ext (Shape M) (@ Pos M) M (M A);
    to_from : forall M A (fx : H M A), to A (from  fx) = fx;
    from_to : forall M A (e : Ext (Shape M) (@Pos M) M (M A)), from (to A e) = e
  }.
Arguments from {_} {_} {_} _.

Section Free.
  Variable M : Type -> Type.
  Variable H : (Type -> Type) -> Type -> Type.

  Inductive Free (HC__F : HContainer H) A :=
  | pure : A -> Free HC__F A
  | impure : Ext (Shape M) (Pos M) M (Free HC__F A) -> Free HC__F A.
End Free.
Arguments pure {_} {_} {_} _.

Section Zero.

  Inductive Void :=.

  Definition Zero (M : Type -> Type) (A : Type) := Void.

  Definition Shape__Zero (M : Type -> Type) := Void.

  Definition Pos__Zero (M : Type -> Type) (s: Shape__Zero M) := Void.

  Definition Ext__Zero M A := Ext (Shape__Zero M) (@Pos__Zero M) M A.

  Definition to__Zero (M : Type -> Type) A (e: Ext__Zero M (M A)) : Zero M A :=
    match e with
      ext s _ => match s with end
    end.

  Definition from__Zero M A (z: Zero M A) : Ext__Zero M (M A) :=
    match z with end.

  Lemma to_from__Zero : forall M A (ox : Zero M A), to__Zero A (from__Zero ox) = ox.
  Proof.
    intros M A ox.
    destruct ox.
  Qed.

  Lemma from_to__Zero : forall M A (e : Ext__Zero M (M A)), from__Zero (to__Zero A e) = e.
  Proof.
    intros M A [s pf].
    destruct s.
  Qed.

  Instance C__Zero : HContainer Zero :=
    {
      Shape := Shape__Zero;
      Pos   := Pos__Zero;
      to    := @to__Zero;
      from  := @from__Zero;
      to_from := @to_from__Zero;
      from_to := @from_to__Zero
    }.

End Zero.

Section Choice.

  Inductive Choice M (A : Type) :=
  | cfail   : Choice M A
  | cchoice : option (nat * nat) -> M A -> M A -> Choice M A.

  Inductive Shape__Choice (M : Type -> Type) :=
  | sfail : Shape__Choice M
  | schoice : option (nat * nat) -> Shape__Choice M.

  Definition Pos__Choice M (s: Shape__Choice M) : Type :=
    match s with
    | sfail _  => Void
    | schoice _ _ => bool
    end.

  Definition Ext__Choice M A := Ext (Shape__Choice M) (@Pos__Choice M) M A.

  Definition to__Choice M A (e: Ext__Choice M (M A)) : Choice M A :=
    match e with
    | ext (sfail _) f   => cfail M A
    | ext (schoice _ mid) f => cchoice M A mid (f true) (f false)
    end.

  Fixpoint from__Choice M A (z : Choice M A) : Ext__Choice M (M A) :=
    match z with
    | cfail _ _     => ext (sfail M) (fun p : Pos__Choice (sfail _) => match p with end)
    | cchoice _ _ mid l r => ext (schoice M mid) (fun p : Pos__Choice (schoice M mid) => if p then l else r)
    end.

  Lemma to_from__Choice : forall M A (ox : Choice M A), to__Choice A (from__Choice ox) = ox.
  Proof.
    intros M A ox.
    destruct ox; reflexivity.
  Qed.

  Lemma from_to__Choice : forall M A (e : Ext__Choice M (M A)), from__Choice (to__Choice A e) = e.
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

  Inductive Shape__State (M : Type -> Type) :=
  | sget : Shape__State M
  | sput : S -> Shape__State M.
  
  Inductive Pos__State M : Shape__State M -> Type :=
  | pget : forall (st : S), Pos__State (sget M)
  | pput : forall (st : S), Pos__State (sput M st).

  Definition Ext__State M A := Ext (Shape__State M) (@Pos__State M) M A.

  Definition to__State M A (e: Ext__State M (M A)) : State M A :=
    match e with
    | ext (sget _)     fp => get M A (fun s => fp (pget M s))
    | ext (sput _ s) fp => put M A s (fp (pput M s))
    end.

  Fixpoint from__State M A (z : State M A) : Ext__State M (M A) :=
    match z with
    | get _ _ f   => ext (sget M)     (fun p : Pos__State (sget M) => match p with pget _ s => f s end)
    | put _ _ s a => ext (sput M s) (fun p : Pos__State (sput M s) => a)
    end.

  Lemma to_from__State : forall M A (ox : State M A), to__State A (from__State ox) = ox.
  Proof.
    intros M A ox.
    destruct ox.
    - simpl. f_equal.
    - reflexivity.
  Qed.

  Lemma from_to__State : forall M A (e : Ext__State M (M A)), from__State (to__State A e) = e.
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
  | ssharing : forall X, nat -> X -> Shape__Sharing M.

  Inductive Pos__Sharing M : Shape__Sharing M -> Type :=
  | psharing : forall X (x : X) (n : nat), Pos__Sharing (ssharing M n x).

  Definition Ext__Sharing M A := Ext (Shape__Sharing M) (@Pos__Sharing M) M A.

  Definition to__Sharing M `(Monad M) A (e: Ext__Sharing M (M A)) : Sharing M A :=
    match e with
    | ext (ssharing _ n x) fp => csharing M A n (ret x) (fun y => fp (psharing M x n))
    end.

  Variable MM : forall M, Monad M.
  
  Fixpoint from__Sharing M A (z : Sharing M A) : Ext__Sharing M (M A) :=
    match z with
    | csharing _ _ n mx xma =>
      ext (ssharing _ n mx) (fun p : Pos__Sharing (ssharing _ n mx)
                               => match p with
                                    psharing _ x m => xma mx
                                  end)
    end.

  Lemma to_from__Sharing : forall M A (ox : Sharing M A), to__Sharing A (from__Sharing ox) = ox.
  Proof.
    intros M A ox.
    destruct ox.
    simpl.
    f_equal.
    extensionality p.
    unfold bind. 
  Admitted.

  Lemma from_to__Sharing : forall M A (e : Ext__Sharing M (M A)),
      from__Sharing (to__Sharing A e) = e.
  Proof.
    intros M A [s pf].
    destruct s.
    simpl.
    f_equal.
    extensionality p.
    dependent destruction p.
  Admitted.

  Instance C__Sharing : HContainer Sharing :=
    {
      Shape := Shape__Sharing;
      Pos   := Pos__Sharing;
      to    := to__Sharing;
      from  := from__Sharing;
      to_from := to_from__Sharing;
      from_to := from_to__Sharing
    }.

End Sharing.

Inductive ChoiceF (A : Type) :=
| cffail   : ChoiceF A
| cfchoice : option (nat * nat) -> A -> A -> A -> ChoiceF A.

Definition Prog M := Free M (C__Choice).
Definition NDShare := C__Choice.

Definition Fail M A : Prog M A :=
  @impure M Choice C__Choice A (ext (sfail M) (fun p : Pos__Choice (sfail M) => match p with end)).

Arguments Fail {_}.

Definition Choice' M A mid l r : Prog M A :=
  let s  := schoice M mid
  in @impure M Choice C__Choice A (ext s (fun p : Pos__Choice s => if p then l else r)).

Fixpoint runChoice M A (fc : Free M C__Choice A) : Tree A :=
  match fc with
  | pure _ x => Leaf x
  | impure (ext (sfail _)   _)  => Empty A
  | impure (ext (schoice _ mid) pf) => Branch mid (runChoice (pf true)) (runChoice (pf false))
  end.

Require Import Lists.List.
Import ListNotations.

Definition handle M A (p : Prog M A) := collectVals (runChoice p).
Definition coin M : Prog M bool := Choice' None (pure bool true) (pure bool false).
Example example1 M : Prog M bool := coin M.
Example res_example1 := [true; false].

Example example2 M : Prog M bool := Choice' None (coin M)  (coin M).
Example res_example2 := [true; false; true; false].

Definition exBs := [(example1, res_example1); (example2, res_example2)].
  
Lemma tests__exBs : Forall (fun '(p,r) => handle (p ChoiceF) = r) exBs.
Proof. repeat econstructor. Qed.

Definition Share' (n : nat) X M `(MM : Monad M) A (fs : Prog M A) : Prog M A :=
  let s : Shape__Sharing (Prog M) := ssharing _ _ n fs
  in @impure _ Sharing (C__Sharing _) A (ext s (fun p : Pos__Sharing s => match p with
                                                                            psharing _ _ n mx => 
                                                                          end)).
