Require Import Thesis.Base.
Require Import Thesis.Container.
Require Import Thesis.Free.

Set Implicit Arguments.

Section Prog.
  Definition NDShare := C__Comb (C__State nat) (C__Comb C__Sharing C__Choice).
  
  Definition NDShare__SC := C__Comb C__Sharing C__Choice.
  
  Definition Prog := Free NDShare.
  
  Definition Prog__SC := Free NDShare__SC.

  Fixpoint fmap__NDShare A B (f : A -> B) (p : Prog A) : Prog B :=
    match p with
    | pure x => pure (f x)
    | impure (ext s pf) => impure (ext s (fun p => fmap__NDShare f (pf p)))
    end.
End Prog.
 
Class Shareable (A : Type) :=
  {
    shareArgs : A -> Prog A
  }.

Class Normalform (A B : Type) :=
  {
    nf : Prog A -> Prog B
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

Notation "x ? y" := (Choice None x y) (at level 80).

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

  Definition dupShare A `{Shareable A} (fx : Prog A) : Prog (Pair A A) :=
    Share fx >>= fun x => pairM x x.

  Definition shrrgs__Pair A B `(Shareable A) `(Shareable B) (p : Pair A B) : Prog (Pair A B) :=
    match p with
    | Pair' a b => Share a >>= fun sa => Share b >>= fun sb => pairM sa sb
    end.

  Global Instance shrbl__Pair A B `(sa : Shareable A) `(sb : Shareable B) : Shareable (Pair A B) :=
    {
      shareArgs := @shrrgs__Pair A B sa sb
    }.

  Definition nf__Pair A B C D `{Normalform A C} `{Normalform B D} (stp : Prog (Pair A B)) : Prog (Pair C D) :=
    stp >>= fun '(Pair' sp1 sp2) =>
              nf sp1 >>= fun b1 =>
                           nf sp2 >>= fun b2 =>
                                        pairM (pure b1) (pure b2).

  Global Instance nrmlfrm__Pair A B C D `{Normalform A C} `{Normalform B D} : Normalform (Pair A B) (Pair C D) :=
    {
      nf := fun x => nf__Pair x
    }.

End Pair.

Section List.
  Inductive List A :=
  | Nil' : List A
  | Cons' : Prog A -> Prog (List A) -> List A.

  Definition consM A (fx : Prog A) (fxs : Prog (List A)) : Prog (List A) :=
    pure (Cons' fx fxs).

  Definition nilM {A} : Prog (List A) := pure (@Nil' A).

  Definition headM A (fxs : Prog (List A)) : Prog A :=
    fxs >>= fun xs => match xs with
                   | Nil' _    => @Fail A
                   | Cons' x _ => x
                   end.

  Definition dupl A (fx : Prog A) : Prog (List A) :=
    consM fx (consM fx (@nilM A)).

  Definition duplShare A `{Shareable A} (fx : Prog A) : Prog (List A) :=
    Share fx >>= fun x => consM x (consM x (@nilM A)).

  Fixpoint appM' A (xs : List A) (fxs : Prog (List A)) : Prog (List A) :=
    match xs with
    | Nil' _       => fxs
    | Cons' fz fzs => consM fz (fzs >>= fun zs => appM' zs fxs)
    end.

  Definition appM A (fxs fys : Prog (List A)) : Prog (List A) :=
    fxs >>= fun xs => appM' xs fys.


  Definition shrrgs__List A `(Shareable A) `(Shareable (List A)) (xs : List A) : Prog (List A) :=
    match xs with
    | Nil' _     => @nilM A
    | Cons' y ys => Share y >>= fun sy => Share ys >>= fun sys => consM sy sys
    end.

  Global Instance shrbl__List A `(sa : Shareable A) : Shareable (List A) :=
    {
      shareArgs := fun xs =>
                     let fix aux xs :=
                         let shr fp := Get >>= fun i =>
                                       Put (i * 2) >>= fun _ =>
                                       pure (Share' i (
                                         Put (i * 2 + 1) >>= fun _ =>
                                         fp >>= fun x => aux x))
                         in
                         match xs with
                         | Nil' _     => @nilM A
                         | Cons' y ys => Share y >>= fun sy => shr ys >>= fun sys => consM sy sys
                         end
                     in aux xs
    }.

  Fixpoint nf'__List A B `{Normalform A B} (xs : List A) : Prog (List B) :=
    match xs with
    | Nil' _ => nilM
    | Cons' sx sxs => nf sx >>= fun x =>
                                 sxs >>= fun xs => nf'__List xs >>= fun xs' =>
                                                                 consM (pure x) (pure xs')
    end.

  Definition nf__List A B `{Normalform A B}  (stxs : Prog (List A)) : Prog (List B) :=
    stxs >>= fun xs => nf'__List xs.

  Global Instance nrmlfrm__List A B `{Normalform A B} : Normalform (List A) (List B) :=
    {
      nf := fun x => nf__List x
    }.

  Fixpoint lengthM A (xs : List A) : Prog nat :=
    match xs with
    | Nil' _ => pure 0
    | Cons' _ fxs =>
      let m := match fxs with
               | pure xs => lengthM xs
               | impure (ext (inl (sget _)) pf) =>
                 pf (pget 42) >>= fun xs => lengthM xs
               | impure (ext (inl (sput s'))   pf) =>
                 pf (pput s') >>= fun xs => lengthM xs
               | impure (ext (inr (inr sfail)) _)  => pure 0
               | impure (ext (inr (inr (schoice mid))) pf) =>
                 (pf true >>= fun xs => lengthM xs) >>= fun x =>
                                                          (pf false >>= fun xs => lengthM xs) >>= fun y => pure (max x y)
               | impure (ext (inr (inl (ssharing n)))  pf) =>
                 pf (psharing n) >>= fun xs => lengthM xs
               end
      in m >>= fun i => pure (i + 1)
    end.

  Fixpoint convert (xs : list nat) : Prog (List nat) :=
    match xs with
    | nil => nilM
    | cons x xs => consM (pure x) (convert xs)
    end.
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

Global Instance nrmlfrm__Nat : Normalform nat nat :=
  {
    nf := fun x => x
  }.

Global Instance nrmlfrm__Bool : Normalform bool bool :=
  {
    nf := fun x => x
  }.
