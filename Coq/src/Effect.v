Require Import Thesis.Base.
Require Import Thesis.Container.
Require Import Thesis.Free.

Set Implicit Arguments.

Section Prog.
  Definition NDShare := C__Comb (C__State nat) (C__Comb C__Sharing C__Choice).
  
  Definition NDShare__SC := C__Comb C__Sharing C__Choice.
  
  Definition Prog := Free NDShare.
  
  Definition Prog__SC := Free NDShare__SC.
End Prog.
 
Class Shareable (A : Type) :=
  {
    shareArgs : A -> Prog A
  }.

Definition Get : Prog nat :=
  let s : @Shape _ NDShare := inl (sget nat)
  in impure (ext s (fun p : @Pos _ NDShare s => match p with pget s => pure s end)).

Definition Put (n : nat) : Prog unit :=
  let s : @Shape _ NDShare := inl (sput n)
  in impure (ext s (fun p : @Pos _ NDShare s => match p with pput s => pure tt end)).

Definition Share' (n : nat) A (fs : Prog A) : Prog A :=
  let s : @Shape _ NDShare := inr (inl (ssharing n))
  in impure (ext s (fun p : @Pos _ NDShare s => fs)).

Definition Share'__SC (n : nat) A (fs : Prog__SC A) : Prog__SC A :=
  let s : @Shape _ NDShare__SC := inl (ssharing n)
  in impure (ext s (fun p : @Pos _ NDShare__SC s => fs)).

Definition Share A `(Shareable A) (fp : Prog A) : Prog (Prog A) :=
  Get >>= fun i => Put (i * 2) >>= fun _=> pure (Share' i (Put (i * 2 + 1) >>= fun _ => fp >>= fun x => shareArgs x)).
Arguments Share {_} {_} fp.

Definition Fail A : Prog A :=
  let s : @Shape _ NDShare := inr (inr sfail)
    in impure (ext s (fun p : @Pos _ NDShare s => match p with end)).

Arguments Fail {_}.

Definition Fail__C A : Free C__Choice A :=
  let s : @Shape _ C__Choice := sfail
  in impure (ext s (fun p : Pos__Choice s => match p with end)).

Arguments Fail__C {_}.

Definition Fail__SC A : Free (C__Comb C__Sharing C__Choice) A :=
  let s : @Shape _ NDShare__SC := inr sfail
  in impure (ext s (fun p : @Pos _ NDShare__SC s => match p with end)).

Arguments Fail__SC {_}.

Definition Choice__C A mid l r : Free C__Choice A :=
  let s : @Shape _ C__Choice := schoice mid
  in impure (ext s (fun p : Pos__Choice s => if p then l else r)).

Definition Choice__SC A mid l r : Prog__SC A :=
  let s : @Shape _ NDShare__SC := inr (schoice mid)
  in impure (ext s (fun p : @Pos _ NDShare__SC s => if p then l else r)).

Definition Choice A mid l r : Prog A :=
  let s : @Shape _ NDShare := inr (inr (schoice mid))
  in impure (ext s (fun p : @Pos _ NDShare s => if p then l else r)).

Section Pair.
  Inductive Pair A B :=
  | Pair' : Prog A -> Prog B -> Pair A B.
  
  Definition pairM A B (fst : Prog A) (snd : Prog B) : Prog (Pair A B) :=
    pure (Pair' fst snd).

  Definition first A B (fp : Prog (Pair A B)) : Prog A :=
    fp >>= fun '(Pair' fst _) => fst.

  Definition second A B (fp : Prog (Pair A B)) : Prog B :=
    fp >>= fun '(Pair' _ snd) => snd.

  Definition dup' (fp : Prog (Pair bool bool)) : Prog (Pair bool bool) :=
    pairM (first fp) (first fp).

  Definition dup A (fx : Prog A) : Prog (Pair A A) :=
    pairM fx fx.

  Definition dupShare A `(Shareable A) (fx : Prog A) : Prog (Pair A A) :=
    Share fx >>= fun x => pairM x x.

  Definition shrrgs__Pair A B `(Shareable A) `(Shareable B) (p : Pair A B) : Prog (Pair A B) :=
    match p with
    | Pair' a b => Share a >>= fun sa => Share b >>= fun sb => pairM sa sb
    end.

  Global Instance shrbl__Pair A B `(sa : Shareable A) `(sb : Shareable B) : Shareable (Pair A B) :=
    {
      shareArgs := @shrrgs__Pair A B sa sb
    }.
End Pair.

Section List.
  Inductive List A :=
  | Nil : List A
  | Cons : Prog A -> Prog (List A) -> List A.

  Definition cons A (fx : Prog A) (fxs : Prog (List A)) : Prog (List A) :=
    pure (Cons fx fxs).

  Definition nil A : Prog (List A) := pure (@Nil A).

  Definition headM A (fxs : Prog (List A)) : Prog A :=
    fxs >>= fun xs => match xs with
                   | Nil _    => @Fail A
                   | Cons x _ => x
                   end.

  Definition dupl A (fx : Prog A) : Prog (List A) :=
    cons fx (cons fx (@nil A)).

  Definition duplShare A `(Shareable A) (fx : Prog A) : Prog (List A) :=
    Share fx >>= fun x => cons x (cons x (@nil A)).

  Fixpoint appM' A (xs : List A) (fxs : Prog (List A)) : Prog (List A) :=
    match xs with
    | Nil _       => fxs
    | Cons fz fzs => cons fz (fzs >>= fun zs => appM' zs fxs)
    end.

  Fixpoint appM A (fxs fys : Prog (List A)) : Prog (List A) :=
    fxs >>= fun xs => appM' xs fys.

  Definition shrrgs__List A `(Shareable A) `(Shareable (List A)) (xs : List A) : Prog (List A) :=
    match xs with
    | Nil _     => @nil A
    | Cons y ys => Share y >>= fun sy => Share ys >>= fun sys => cons sy sys
    end.
  
  Global Instance shrbl__List A `(sa : Shareable A) (sas : Shareable (List A)) : Shareable (List A) :=
    {
      shareArgs := @shrrgs__List A sa sas
    }.
End List.

Section Prim.
  Definition Coin : Prog nat := Choice None (pure 0) (pure 1).
  Definition Coin__Bool : Prog bool := Choice None (pure true) (pure false).
  
  Definition addM (fn1 fn2 : Prog nat) : Prog nat :=
    fn1 >>= fun n1 => fn2 >>= fun n2 => pure (n1 + n2).
  
  Definition orM (fn1 fn2 : Prog bool) : Prog bool :=
    fn1 >>= fun b => match b with
                  | true => pure true
                  | false => fn2
                  end.
  
  Definition duplicate A (fx : Prog A) : Prog (A * A) :=
    fx >>= fun x => fx >>= fun y => pure (x,y).
End Prim.

Global Instance shrbl__Nat : Shareable nat :=
  {
    shareArgs := pure
  }.

Global Instance shrbl__Bool : Shareable bool :=
  {
    shareArgs := pure
  }.