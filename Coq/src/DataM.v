Require Import Thesis.Free.
Require Import Thesis.Effect.
Require Import Thesis.Base.

Set Implicit Arguments.

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

  Definition dupShare A (fx : Prog A) : Prog (Pair A A) :=
    Share fx >>= fun x => pairM x x.
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
                   | Nil _    => Fail
                   | Cons x _ => x
                   end.

  Definition dupl A (fx : Prog A) : Prog (List A) :=
    cons fx (cons fx (@nil A)).

  Definition duplShare A (fx : Prog A) : Prog (List A) :=
    Share fx >>= fun x => cons x (cons x (@nil A)).

  (* Fixpoint appM A (fxs fys : Prog (List A)) : Prog (List A) := *)
  (*   fxs >>= fun xs => match xs with *)
  (*                  | Nil _       => fys *)
  (*                  | Cons fz fzs => cons fz (appM fzs fys) *)
  (*                  end. *)

End List.