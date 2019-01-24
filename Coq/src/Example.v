Require Import Thesis.Handler.
Require Import Thesis.Effect.
Require Import Thesis.Free.
Require Import Thesis.Base.
Require Import Lists.List.
Require Import EqNat.

Import List.ListNotations.

Set Implicit Arguments.

Definition coin := Coin__Bool.
Definition share := Share.
Definition const := fun A (x _ : A) => x.

Section exB.
  Example example1 : Prog bool := coin.
  Example res_example1 := [true; false].

  Example example2 : Prog bool := coin ? coin.
  Example res_example2 := [true; false; true; false].
  
  Example example3 : Prog bool :=  share coin >>= fun fx => fx ? fx.
  Example res_example3 := res_example2.
  
  Example exOr0 : Prog bool := orM coin (pure false).
  Example res_exOr0 := [true; false].
  
  Example exOr1 : Prog bool := orM coin coin.
  Example res_exOr1 := [true; true; false].
  
  Example exOr2 : Prog bool := share coin >>= fun fx => orM fx fx.
  Example res_exOr2 := [true; false].
  
  Example exOr2a : Prog bool :=
    share coin >>= fun fx => orM (pure false) (orM fx fx).
  Example res_exOr2a := [true; false].
  
  Example exOr2b : Prog bool :=
    share coin >>= fun fx => orM (pure true) (orM fx fx).
  Example res_exOr2b := [true].
  
  Example exOr3 : Prog bool := orM (coin ? coin) (pure true).
  Example res_exOr3 := [true; true; true; true].
  
  Example exOr3a : Prog bool := orM (coin ? coin) coin.
  Example res_exOr3a := [true; true; false; true; true; false].
  
  Example exOr3b : Prog bool := orM coin (coin ? coin).
  Example res_exOr3b := [true; true; false; true; false].
  
  Example exOr3c : Prog bool := orM (coin ? coin) (coin ? coin).
  Example res_exOr3c := [true; true; false; true; false; true; true; false; true; false].
  
  (* here we share, even though nothing is shared *)
  Example exOr4 : Prog bool := share coin >>= fun fx => orM fx coin.
  Example res_exOr4 := [true; true; false].
  
  Example exOrShare : Prog bool := share coin >>= fun fx => orM coin fx.
  Example res_exOrShare := [true; true; false].
  
  Example exOr6 : Prog bool := share coin >>= fun fx => orM fx (orM fx coin).
  Example res_exOr6 := [true; true; false].
  
  Example exOr7 : Prog bool := share coin >>= fun fx => orM coin (orM fx fx).
  Example res_exOr7 := [true; true; false].
  
  Example exOr7a : Prog bool := share coin >>= fun fx => orM (pure true) (orM fx fx).
  Example res_exOr7a := [true].
  
  Example exOr7b : Prog bool := share coin >>= fun fx => orM (pure false) (orM fx fx).
  Example res_exOr7b := [true; false].
  
  Example exShareConst : Prog bool := share coin >>= fun fx => const fx fx.
  Example res_exShareConst := [true; false].
  
  Example exShareConstOrR : Prog bool := share coin >>= fun fx => orM fx (const fx fx).
  Example res_exShareConstOrR := [true; false].
  
  Example exShareConstOrL : Prog bool := share coin >>= fun fx => orM (const fx fx) fx.
  Example res_exShareConstOrL := [true; false].
  
  Example exShareConstOrR2 : Prog bool := share coin >>= fun fx => orM (pure true) (const fx fx).
  Example res_exShareConstOrR2 := [true].
  
  Example exFailed : Prog bool := share Fail >>= fun fx => const (pure true) fx.
  Example res_exFailed := [true].
  
  Example exHead : Prog bool := headM (consM coin Fail).
  Example res_exHead := [true; false].
  
  Example exOrShareShare : Prog bool :=
    share coin >>=
          fun fx =>
            share coin >>=
                  fun fy =>
                    orM fx (orM fy (orM fx fy)).
  Example res_exOrShareShare := [true; true; false].
  
  Example exOrShareNested : Prog bool :=
    share coin >>= fun fx =>
                     orM fx (share coin >>= fun fy =>
                                              orM fy (orM fx fy)).
  Example res_exOrShareNested := [true; true; false].
  
  Example exShareNestedChoiceOr : Prog bool :=
    share ((pure true ? pure false) ? (pure true ? pure false)) >>=
          fun fx => orM fx fx.
  Example res_exShareNestedChoiceOr := [true; false; true; false].
  
  Example exShareIgnoreShare : Prog bool :=
    share coin >>= fun fx => const (pure true) (share fx >>= fun fy => orM fy fy).
  Example res_exShareIgnoreShare := [true].
  
  Example exRepeatedShare : Prog bool :=
    share coin >>= fun fx => share fx >>= fun fy => orM fy fy.
  Example res_exRepeatedShare := [true; false].
  
  Definition exBs := [(example1, res_example1);
                        (example2, res_example2);
                        (example3, res_example3);
                        (exOr0, res_exOr0);
                        (exOr1, res_exOr1);
                        (exOr2, res_exOr2);
                        (exOr2a, res_exOr2a);
                        (exOr2b, res_exOr2b);
                        (exOr3, res_exOr3);
                        (exOr3a, res_exOr3a);
                        (exOr3b, res_exOr3b);
                        (exOr3c, res_exOr3c);
                        (exOr4, res_exOr4);
                        (exOrShare, res_exOrShare);
                        (exOr6, res_exOr6);
                        (exOr7, res_exOr7);
                        (exOr7a, res_exOr7a);
                        (exOr7b, res_exOr7b);
                        (exShareConst, res_exShareConst);
                        (exShareConstOrR, res_exShareConstOrR);
                        (exShareConstOrL, res_exShareConstOrL);
                        (exShareConstOrR2, res_exShareConstOrR2);
                        (exFailed, res_exFailed);
                        (exHead, res_exHead);
                        (exOrShareShare, res_exOrShareShare);
                        (exOrShareNested, res_exOrShareNested);
                        (exShareNestedChoiceOr, res_exShareNestedChoiceOr);
                        (exShareIgnoreShare, res_exShareIgnoreShare);
                        (exRepeatedShare, res_exRepeatedShare)].
  
  Lemma tests__exBs : Forall (fun '(p,r) => handle p = r) exBs.
  Proof. repeat econstructor. Qed.
End exB.

Section exPB.
  Example exDup : Prog (Pair bool bool) := dup coin.
  Example res_exDup := [Pair' (pure true) (pure true)
                        ; Pair' (pure true) (pure false)
                        ; Pair' (pure false) (pure true)
                        ; Pair' (pure false) (pure false)].
  
  Example exDupShare : Prog (Pair bool bool) := share coin >>= fun x => dup x.
  Example res_exDupShare := [Pair' (pure true) (pure true)
                             ; Pair' (pure false) (pure false)].
  
  Example exDupShare2 : Prog (Pair bool bool) := dupShare coin.
  Example res_exDupShare2 := [Pair' (pure true) (pure true)
                              ; Pair' (pure false) (pure false)].
  
  Example exDupFailed : Prog (Pair bool bool) := share Fail >>= fun x => dup (const (pure true) x).
  Example res_exDupFailed := [Pair' (pure true) (pure true)].
  
  Example exDupFirst : Prog (Pair bool bool) := dup (@first bool bool (pairM coin Fail)).
  Example res_exDupFirst := [Pair' (pure true) (pure true)
                             ; Pair' (pure true) (pure false)
                             ; Pair' (pure false) (pure true)
                             ; Pair' (pure false) (pure false)].
  
  Example exDupShareFirst : Prog (Pair bool bool) := dupShare (@first bool bool (pairM coin Fail)).
  Example res_exDupShareFirst :=  [Pair' (pure true) (pure true); Pair' (pure false) (pure false)].
  
  Example exShareNestedChoice : Prog (Pair bool bool) :=
    share ((pure true ? pure false) ? (pure true ? pure false)) >>=
          fun fx => pairM fx fx.
  Example res_exShareNestedChoice := [Pair' (pure true) (pure true) 
                                      ; Pair' (pure false) (pure false)
                                      ; Pair' (pure true) (pure true)
                                      ; Pair' (pure false) (pure false)].
  
  Definition exPBs := [(exDup, res_exDup)
                       ; (exDupShare, res_exDupShare)
                       ; (exDupShare2, res_exDupShare2)
                       ; (exDupFailed, res_exDupFailed)
                       ; (exDupFirst, res_exDupFirst)
                       ; (exDupShareFirst, res_exDupShareFirst)
                       ; (exShareNestedChoice, res_exShareNestedChoice)].

  Lemma tests__exPBs : Forall (fun '(p,r) => handle p = r) exPBs.
  Proof. repeat econstructor. Qed.
End exPB.

Section exLB.
  Arguments nilM {_}.
  Arguments Nil' {_}.

  Example exDupl : Prog (List bool) := dupl (headM (consM coin Fail)).
  Example res_exDupl := [Cons' (pure true) (consM (pure true) nilM)
                         ; Cons' (pure true) (consM (pure false) nilM)
                         ; Cons' (pure false) (consM (pure true) nilM)
                         ; Cons' (pure false) (consM (pure false) nilM)].

  Example exDupl2 : Prog (List bool) := consM (headM (consM coin Fail))
                                           (consM (headM (consM coin Fail)) nilM).
  Example res_exDupl2 := [Cons' (pure true) (consM (pure true) nilM)
                          ; Cons' (pure true) (consM (pure false) nilM)
                          ; Cons' (pure false) (consM (pure true) nilM)
                          ; Cons' (pure false) (consM (pure false) nilM)].

  Example exDuplShare : Prog (List bool) := duplShare (headM (consM coin Fail)).
  Example res_exDuplShare := [Cons' (pure true) (consM (pure true) nilM)
                              ; Cons' (pure false) (consM (pure false) nilM)].

  Example exShareNestedChoice2 : Prog (List bool) :=
    share (pure true ? coin) >>=
          fun fx => share coin >>= fun fy => consM fx (consM fy (consM fx (consM fy nilM))).

  Example res_exShareNestedChoice2 :=
    [Cons' (pure true) (consM (pure true) (consM (pure true) (consM (pure true) nilM)))
     ; Cons' (pure true) (consM (pure false) (consM (pure true) (consM (pure false) nilM)))
     ; Cons' (pure true) (consM (pure true) (consM (pure true) (consM (pure true) nilM)))
     ; Cons' (pure true) (consM (pure false) (consM (pure true) (consM (pure false) nilM)))
     ; Cons' (pure false) (consM (pure true) (consM (pure false) (consM (pure true) nilM)))
     ; Cons' (pure false) (consM (pure false) (consM (pure false) (consM (pure false) nilM)))].

  Example exOrShareNestedList : Prog (List bool) :=
    share coin >>= fun fx =>
                     consM fx (share coin >>= fun fy =>
                                                consM fy (consM fx (consM fy nilM))).
  Example res_exOrShareNestedList :=
    [Cons' (pure true) (consM (pure true) (consM (pure true) (consM (pure true) nilM)))
     ; Cons' (pure true) (consM (pure false) (consM (pure true) (consM (pure false) nilM)))
     ; Cons' (pure false) (consM (pure true) (consM (pure false) (consM (pure true) nilM)))
     ; Cons' (pure false) (consM (pure false) (consM (pure false) (consM (pure false) nilM)))].

  Definition exLBs := [(exDupl, res_exDupl)
                       ; (exDupl2,  res_exDupl2)
                       ; (exDuplShare, res_exDuplShare)
                       ; (exShareNestedChoice2, res_exShareNestedChoice2)
                       ; (exOrShareNestedList, res_exOrShareNestedList)].

  Lemma tests__exLBs : Forall (fun '(p,r) => handle p = r) exLBs.
  Proof. repeat econstructor. Qed.

End exLB.
              
Section exLPB.

 Example exShareSingleton : Prog (Pair (List bool) (List bool)) :=
   Share (consM (pure true ? pure false) nilM) >>= fun fx => pairM fx fx.
 Example res_exShareSingleton := [Pair' (pure (Cons' (pure true) nilM))
                                        (pure (Cons' (pure true) nilM))
                                  ; Pair' (pure (Cons' (pure false) nilM))
                                          (pure (Cons' (pure false) nilM))].

   Fixpoint recList' (n : nat) (xs : List bool) : Prog (List bool) :=
     match n with
     | 0 => Fail
     | S n => match xs with
             | Nil' _ => nilM
             | Cons' fy fys =>
               Share fys >>= fun fys' => consM fy (fys' ? fys' >>= fun zs => recList' n zs)
             end
     end.

   Fixpoint lengthHelp A (xs : List A) : nat :=
     match xs with
     | Nil' _ => 0
     | Cons' _ fxs => 1 + match fxs with
                         | pure xs => lengthHelp xs
                         | _ => 0
                         end
     end.
   
   Definition recList (fxs : Prog (List bool)) : Prog (List bool) :=
     fxs >>= fun xfps => recList' (lengthHelp xfps)  xfps.

   Example exRecList : Prog (Pair (List bool) (List bool)) :=
     Share (recList (consM (pure true) (consM (pure false) nilM))) >>= fun fx => pairM fx fx.
   Example res_exRecList := [Pair' (consM (pure true) (consM (pure false) nilM))
                                   (consM (pure true) (consM (pure false) nilM))
                             ; Pair' (consM (pure true) (consM (pure false) nilM))
                                     (consM (pure true) (consM (pure false) nilM))
                             ; Pair' (consM (pure true) (consM (pure false) nilM))
                                     (consM (pure true) (consM (pure false) nilM))].

   Definition exLPBs := [(exShareSingleton, res_exShareSingleton)
                         ; (exRecList, res_exRecList)].
   
  Lemma tests__exLPBs : Forall (fun '(p,r) => handle p = r) exLBs.
  Proof. repeat econstructor. Qed.
End exLPB.

Section Extra.
  Example exSkipIds : Prog bool :=
    Share coin >>= fun fx => const coin (const fx fx).
  Example res_exSkipIds := [true; false].

  Lemma lem_exSkipIDs : handle exSkipIds = res_exSkipIds.
  Proof. reflexivity. Qed.

  Example exShareInShare : Prog (Pair bool bool) :=
    Share (Share coin >>= fun fx => orM fx fx) >>= fun fy => pairM fy fy.
  Example res_exShareInShare := [Pair' (pure true) (pure true)
                                 ; Pair' (pure false) (pure false)].
  Lemma lem_exShareInShare : handle exShareInShare = res_exShareInShare.
  Proof. reflexivity. Qed.

  Example exShareListInShare : Prog (Pair (List bool) (List bool)) :=
    Share (Share (consM coin (consM coin nilM)) >>=
                 fun fx => appM fx fx) >>= fun fy => pairM fy fy.
  
  Example res_exShareListInShare :=
    [Pair' (consM (pure true) (consM (pure true) (consM (pure true) (consM (pure true) nilM))))
           (consM (pure true) (consM (pure true) (consM (pure true) (consM (pure true) nilM))))
     ; Pair' (consM (pure true) (consM (pure false) (consM (pure true) (consM (pure false) nilM))))
             (consM (pure true) (consM (pure false) (consM (pure true) (consM (pure false) nilM))))
     ; Pair' (consM (pure false) (consM (pure true) (consM (pure false) (consM (pure true) nilM))))
             (consM (pure false) (consM (pure true) (consM (pure false) (consM (pure true) nilM))))
     ; Pair' (consM (pure false) (consM (pure false) (consM (pure false) (consM (pure false) nilM))))
             (consM (pure false) (consM (pure false) (consM (pure false) (consM (pure false) nilM))))].
  Lemma lem_exShareListInShare : handle exShareListInShare = res_exShareListInShare.
  Proof. reflexivity. Qed.

  Example exSharePutPos : Prog (List bool) :=
    Share (Share (consM coin nilM) >>= fun fx => appM fx fx) >>= fun fy => appM fy fy.
  
  Example res_exSharePutPos := [Cons' (pure true) (consM (pure true) (consM (pure true) (consM (pure true) nilM)))
                                ; Cons'  (pure false) (consM (pure false) (consM (pure false) (consM (pure false) nilM)))].
  Lemma lem_exSharePutPos : handle exSharePutPos = res_exSharePutPos.
  Proof. reflexivity. Qed.

  Example exShareListInRepeatedShare : Prog (List bool) :=
    Share (Share (consM coin nilM) >>= fun fx => appM fx fx) >>=
          fun fy => Share coin >>= fun fz => Share coin >>= fun fa => consM fz (consM fa fy).
  Example res_exShareListInRepeatedShare :=
    [Cons' (pure true) (consM (pure true) (consM (pure true) (consM (pure true) nilM)))
     ; Cons' (pure true) (consM (pure true) (consM (pure false) (consM (pure false) nilM)))
     ;  Cons' (pure true) (consM (pure false) (consM (pure true) (consM (pure true) nilM)))
     ;  Cons' (pure true) (consM (pure false) (consM (pure false) (consM (pure false) nilM)))
     ;  Cons' (pure false) (consM (pure true) (consM (pure true) (consM (pure true) nilM)))
     ;  Cons' (pure false) (consM (pure true) (consM (pure false) (consM (pure false) nilM)))
     ;  Cons' (pure false) (consM (pure false) (consM (pure true) (consM (pure true) nilM)))
     ;  Cons' (pure false) (consM (pure false) (consM (pure false) (consM (pure false) nilM)))].
  Lemma lem_exShareListInRepeatedShare : handle exShareListInRepeatedShare = res_exShareListInRepeatedShare.
  Proof. reflexivity. Qed.
End Extra.

Section PermSort.

  (* Fixpoint insert' (e : Prog nat) (l : List nat) : Prog (List nat) := *)
  (*   match l with *)
  (*   | Cons' x xs => xs >>= fun xs' => consM x (insert' e xs') *)
  (*   | Nil' _     => Fail *)
  (*   end. *)

  (* Definition insert (e : Prog nat) (l : Prog (List nat)) : Prog (List nat) := *)
  (*   Share e >>= fun e' => *)
  (*                (consM e' l) ? (l >>= fun ys => insert' e' ys). *)

  Fixpoint insert' (e : Prog nat) (ys : List nat) : Prog (List nat) :=
    consM e (pure ys) ? match ys with
                | Cons' x xs => xs >>= fun xs' => consM x (insert' e xs')
                | Nil' _     => Fail
                end.

  Definition insert (e : Prog nat) (l : Prog (List nat)) : Prog (List nat) :=
    Share e >>= fun e' => l >>= fun ys => insert' e' ys.

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
    | Cons' my mys => mx >>= fun x => my >>= fun y => mys >>= fun ys => if Nat.leb x y then isSorted'' (pure y) ys
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
  
  Fixpoint convert (xs : list nat) : Prog (List nat) :=
    match xs with
    | nil => nilM
    | cons x xs => consM (pure x) (convert xs)
    end.
  
  Definition testList1 := convert [5;42;3;1].
  Definition testList2 := convert [5;42;3;1;1337;51;123;125].
  Definition testList3 := convert [5;42;3;1;1337;51;123;125;347;174;1000].

  Compute handle (sort testList1). (* works! *)
  (* Compute handle (sort testList2). (* might takes a while *) *)
  (* Compute handle (sort testList3). (* does it even terminate? *) *)
End PermSort.