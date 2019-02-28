Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Inductive Ext
          Shape
          (Pos : Shape -> Type)
          (PosX : Shape -> Type)
          (Ctx : forall s : Shape, PosX s -> Type)
          (F : Type -> Type)
          A :=
  ext : forall s, (Pos s -> F A) -> (forall p : PosX s, F (Ctx s p)) -> Ext Shape Pos PosX Ctx F A.

Arguments ext {_ _ _ _ _ _} s pf pfx.

Set Implicit Arguments.

Class HContainer (H : (Type -> Type) -> Type -> Type) :=
  {
    Shape   : Type;
    Pos     : Shape -> Type;
    PosX   : Shape -> Type;
    Ctx     : forall s : Shape, PosX s -> Type;
    to      : forall F A, Ext Shape Pos PosX Ctx F A -> H F A;
    from    : forall F A, H F A -> Ext Shape Pos PosX Ctx F A;
    to_from : forall F A (fx : H F A), to (from fx) = fx;
    from_to : forall F A (e : Ext Shape Pos PosX Ctx F A), from (to e) = e
  }.

Inductive Void :=.

Section Zero.

  Definition Zero (M : Type -> Type) (A : Type) := Void.

  Definition Shape__Zero := Void.

  Definition Pos__Zero (s : Shape__Zero) := Void.

  Definition PosX__Zero (S : Shape__Zero) := Void.

  Definition Ctx__Zero (s : Shape__Zero) : Pos__Zero s -> Type :=
    match s with end.

  Definition Ext__Zero := Ext Shape__Zero Pos__Zero PosX__Zero Ctx__Zero.

  Definition to__Zero F A (e: Ext__Zero F A) : Zero F A :=
    match e with
      ext s _ _ => match s with end
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

Section Combination.

  Variable H1 H2 : (Type -> Type) -> Type -> Type.
  Variable C1 : HContainer H1.
  Variable C2 : HContainer H2.

  Inductive Comb F A : Type :=
  | Inl : H1 F A -> Comb F A
  | Inr : H2 F A -> Comb F A.

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

  Definition Shape__Comb : Type := sum (@Shape H1 C1) (@Shape H2 C2).

  Definition Pos__Comb : Shape__Comb -> Type := fold_sum' (@Pos H1 C1) (@Pos H2 C2).

  Definition PosX__Comb : Shape__Comb -> Type := fold_sum' (@PosX H1 C1) (@PosX H2 C2).
    
  Definition Ctx__Comb (s : Shape__Comb) (p : PosX__Comb s) : Type.
    destruct s;
      apply Ctx with (s0 := s);
      apply p.
  Defined.

  Definition Ext__Comb := Ext Shape__Comb Pos__Comb PosX__Comb Ctx__Comb.

  Definition to__Comb F A (e: Ext__Comb F A) : Comb F A :=
    match e with
    | ext (inl s1) pf pfx => Inl (to (ext s1 pf pfx))
    | ext (inr s2) pf pfx => Inr (to (ext s2 pf pfx))
    end.

  Fixpoint from__Comb F A (z : Comb F A) : Ext__Comb F A :=
    match z with
    | Inl fa => match from F A fa with
                 ext s1 pf1 pfx1 => ext (inl s1) pf1 pfx1
               end
    | Inr ga => match from F A ga with
                 ext s2 pf2 pfx2 => ext (inr s2) pf2 pfx2
               end
    end.

  Lemma to_from__Comb : forall F A (ox : Comb F A), to__Comb (from__Comb ox) = ox.
  Proof.
    intros F A ox.
    destruct ox as [f|f];
      (simpl;
       destruct (from F A f) eqn:H;
       unfold to__Comb;
       rewrite <- H;
       rewrite to_from;
       reflexivity).
  Qed.

  Lemma from_to__Comb : forall F A (e : Ext__Comb F A), from__Comb (to__Comb e) = e.
  Proof.
    intros F A [s pf].
    destruct s; (simpl; rewrite from_to; reflexivity).
  Qed.

  Instance C__Comb : HContainer Comb :=
    {
      Shape := Shape__Comb;
      Pos   := Pos__Comb;
      Ctx   := Ctx__Comb;
      to    := to__Comb;
      from  := from__Comb;
      to_from := to_from__Comb;
      from_to := from_to__Comb
    }.

End Combination.

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

  Definition PosX__Choice (s: Shape__Choice) : Type := Void.


  Definition Ctx__Choice (s : Shape__Choice) : PosX__Choice s -> Type := fun _ => unit.

  Definition Ext__Choice := Ext Shape__Choice Pos__Choice PosX__Choice Ctx__Choice.

  Definition to__Choice F A (e: Ext__Choice F A) : Choice F A :=
    match e with
    | ext sfail _ _   => cfail F A
    | ext (schoice mid) pf _ => cchoice F A mid (pf true) (pf false)
    end.

  Fixpoint from__Choice F A (z : Choice F A) : Ext__Choice F A :=
    match z with
    | cfail _ _           => ext sfail  (fun p : Pos__Choice sfail => match p with end)
                                (fun p : PosX__Choice sfail => match p with end)
    | cchoice _ _ mid l r => ext (schoice mid) (fun p : Pos__Choice (schoice mid) => if p then l else r)
                                (fun p : PosX__Choice (schoice mid) => match p with end)
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
    - destruct p; reflexivity.
    - destruct p.
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

  Definition PosX__State : Shape__State -> Type := fun _ => Void.

  Definition Ctx__State (s : Shape__State) : PosX__State s -> Type := fun _ => unit.

  Definition Ext__State := Ext Shape__State Pos__State PosX__State Ctx__State.

  Definition to__State F A (e: Ext__State F A) : State F A :=
    match e with
    | ext sget     fp _ => get F A (fun s => fp (pget s))
    | ext (sput s) fp _ => put F A s (fp (pput s))
    end.

  Fixpoint from__State F A (z : State F A) : Ext__State F A :=
    match z with
    | get _ _ f   => ext sget     (fun p : Pos__State sget => match p with pget s => f s end)
                        (fun p : PosX__State sget => match p with end)
    | put _ _ s a => ext (sput s) (fun p : Pos__State (sput s) => a)
                        (fun p : PosX__State sget => match p with end)
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
  | pcont   : shapeType s -> Pos__Sharing s.

  Inductive PosX__Sharing (s : Shape__Sharing) : Type :=
  | pshared : PosX__Sharing s.

  Definition Ctx__Sharing (s : Shape__Sharing) (p : PosX__Sharing s) : Type :=
    match p with
    | pshared _ => shapeType s
    end.

  Definition Ext__Sharing := Ext Shape__Sharing Pos__Sharing PosX__Sharing Ctx__Sharing.

  Definition to__Sharing F A (e: Ext__Sharing F A) : Sharing F A :=
    match e with
    | ext (ssharing n _ as s) fp fpx => csharing F A n (fpx (pshared s)) (fun x => fp (pcont s x))
    end.

  Definition from__Sharing F A (z : Sharing F A) : Ext__Sharing F A.
    destruct z.
    apply ext with (s := ssharing p X).
    - intros.
      destruct X0.
      + apply f0.
        apply s.
    - intros.
      destruct p0.
      + simpl. apply f.
  Defined.

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
