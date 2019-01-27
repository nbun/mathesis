Require Import Thesis.Prog.
Require Import Thesis.Base.
Require Import Thesis.Effect.
Require Import Thesis.Classes.

Set Implicit Arguments.

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

  Global Instance shareable__Nat : Shareable nat :=
    {
      shareArgs := pure
    }.
  
  Global Instance shareable__Bool : Shareable bool :=
    {
      shareArgs := pure
    }.
  
  Global Instance normalform__Nat : Normalform nat nat :=
    {
      nf := fun x => x
    }.
  
  Global Instance normalform__Bool : Normalform bool bool :=
    {
      nf := fun x => x
    }.
End Prim.

Section Pair.
  Inductive Pair A B :=
  | Pair' : Prog A -> Prog B -> Pair A B.
  
  Definition pairM A B (fst : Prog A) (snd : Prog B) : Prog (Pair A B) :=
    pure (Pair' fst snd).

  Definition firstM A B (fp : Prog (Pair A B)) : Prog A :=
    fp >>= fun '(Pair' fst _) => fst.

  Definition secondM A B (fp : Prog (Pair A B)) : Prog B :=
    fp >>= fun '(Pair' _ snd) => snd.

  Definition dup' (fp : Prog (Pair bool bool)) : Prog (Pair bool bool) :=
    pairM (firstM fp) (firstM fp).

  Definition dup A (fx : Prog A) : Prog (Pair A A) :=
    pairM fx fx.

  Definition dupShare A `{Shareable A} (fx : Prog A) : Prog (Pair A A) :=
    Share fx >>= fun x => pairM x x.

  Definition shrrgs__Pair A B `(Shareable A) `(Shareable B) (p : Pair A B) : Prog (Pair A B) :=
    match p with
    | Pair' a b => Share a >>= fun sa => Share b >>= fun sb => pairM sa sb
    end.

  Global Instance shareable__Pair A B `(sa : Shareable A) `(sb : Shareable B) : Shareable (Pair A B) :=
    {
      shareArgs := @shrrgs__Pair A B sa sb
    }.

  Definition nf__Pair A B C D `{Normalform A C} `{Normalform B D} (stp : Prog (Pair A B)) : Prog (Pair C D) :=
    stp >>= fun '(Pair' sp1 sp2) =>
              nf sp1 >>= fun b1 =>
                           nf sp2 >>= fun b2 =>
                                        pairM (pure b1) (pure b2).

  Global Instance normalform__Pair A B C D `{Normalform A C} `{Normalform B D} : Normalform (Pair A B) (Pair C D) :=
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

  Global Instance shareable__List A `(sa : Shareable A) : Shareable (List A) :=
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

  Global Instance normalform__List A B `{Normalform A B} : Normalform (List A) (List B) :=
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
