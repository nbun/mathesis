Require Import Thesis.Base.
Require Import Thesis.Effect.
Require Import Thesis.Prog.
Require Import Thesis.Handler.
Require Import Thesis.DataM.
Require Import Lists.List.

Import ListNotations.

Section PermSort.
  Fixpoint insert' fx xs : Prog (List nat) :=
    match xs with
    | Nil' _ => Fail
    | Cons' fy fys => consM fy ((consM fx fys) ? (fys >>= insert' fx))
    end.
  
  Definition insert (fx : Prog nat) (fxs : Prog (List nat)) : Prog (List nat) :=
    Share fx >>= fun fx' => (consM fx' fxs) ? (fxs >>= insert' fx').

  Fixpoint perm' (xs : List nat) : Prog (List nat) :=
    match xs with
    | Nil' _ => nilM
    | Cons' mx mxs => mxs >>= fun mxs' => insert mx (perm' mxs')
    end.

  Definition perm (mxs : Prog (List nat)) : Prog (List nat) :=
    mxs >>= perm'.

  Fixpoint isSorted'' (mx : Prog nat) (xs : List nat) : Prog bool :=
    match xs with
    | Nil' _ => pure true
    | Cons' my mys => mx >>= fun x => my >>= fun y =>
                       if Nat.leb x y
                         then mys >>= fun ys => isSorted'' (pure y) ys
                         else pure false
    end.

  Fixpoint isSorted' (mx : Prog nat) (mxs : Prog (List nat)) : Prog bool :=
    mxs >>= fun xs => isSorted'' mx xs.

  Definition isSorted (mxs : Prog (List nat)) : Prog bool :=
    mxs >>= fun xs => match xs with
                   | Nil' _ => pure true
                   | Cons' my mys => isSorted' my mys
                   end.
  
  Definition sort (l : Prog (List nat)) : Prog (List nat) :=
    Share (perm l) >>= fun xs => isSorted xs >>= fun b => if b then xs else Fail.
  
  Inductive sorted : List nat -> Prop :=
  | sort_nil  : sorted (Nil' nat)
  | sort_singleton : forall n, sorted (Cons' (pure n) nilM)
  | sort_cons : forall n m ns, le n m -> sorted (Cons' (pure n) (consM (pure m) ns)).

  Inductive singleton {A} : list A -> Prop :=
  | singletn : forall (x : A), singleton [x].

  Definition testList := convert [5;42;3;1].

  Lemma sorted_testList : let xs := handle (sort testList) in Forall sorted xs /\ singleton xs.
    Proof. repeat econstructor. Qed.
End PermSort.