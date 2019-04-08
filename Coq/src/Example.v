(** Test suite *)
Require Import Thesis.DataM.
Require Import Thesis.Effect.
Require Import Thesis.Handler.
Require Import Thesis.Prog.

Require Import Lists.List.

Import List.ListNotations.

Set Implicit Arguments.

Definition coin := Coin__Bool.
Definition share := Share.
Definition T : Prog bool := pure true.
Definition F : Prog bool := pure false.
Definition const := fun A (x _ : A) => x.

(** Examples for programs that return Boolean values *)
Section exB.
  Example example1 : Prog bool := coin.
  Example res_example1 := [true; false].

  Example example2 : Prog bool := coin ? coin.
  Example res_example2 := [true; false; true; false].
  
  Example example3 : Prog bool :=  share coin >>= fun fx => fx ? fx.
  Example res_example3 := [true; false; true; false].
  
  Example exOr0 : Prog bool := orM coin F.
  Example res_exOr0 := [true; false].
  
  Example exOr1 : Prog bool := orM coin coin.
  Example res_exOr1 := [true; true; false].
  
  Example exOr2 : Prog bool := share coin >>= fun fx => orM fx fx.
  Example res_exOr2 := [true; false].
  
  Example exOr2a : Prog bool :=
    share coin >>= fun fx => orM F (orM fx fx).
  Example res_exOr2a := [true; false].
  
  Example exOr2b : Prog bool :=
    share coin >>= fun fx => orM T (orM fx fx).
  Example res_exOr2b := [true].
  
  Example exOr3 : Prog bool := orM (coin ? coin) T.
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
  
  Example exOr7a : Prog bool := share coin >>= fun fx => orM T (orM fx fx).
  Example res_exOr7a := [true].
  
  Example exOr7b : Prog bool := share coin >>= fun fx => orM F (orM fx fx).
  Example res_exOr7b := [true; false].
  
  Example exShareConst : Prog bool := share coin >>= fun fx => const fx fx.
  Example res_exShareConst := [true; false].
  
  Example exShareConstOrR : Prog bool := share coin >>= fun fx => orM fx (const fx fx).
  Example res_exShareConstOrR := [true; false].
  
  Example exShareConstOrL : Prog bool := share coin >>= fun fx => orM (const fx fx) fx.
  Example res_exShareConstOrL := [true; false].
  
  Example exShareConstOrR2 : Prog bool := share coin >>= fun fx => orM T (const fx fx).
  Example res_exShareConstOrR2 := [true].
  
  Example exFailed : Prog bool := share Fail >>= fun fx => const T fx.
  Example res_exFailed := [true].
  
  Example exHead : Prog bool := headM (consM coin Fail).
  Example res_exHead := [true; false].
  
  Example exOrShareShare : Prog bool :=
    share coin >>= fun fx =>
    share coin >>= fun fy =>
      orM fx (orM fy (orM fx fy)).
  Example res_exOrShareShare := [true; true; false].
  
  Example exOrShareNested : Prog bool :=
    share coin >>= fun fx =>
    orM fx (share coin >>= fun fy =>
      orM fy (orM fx fy)).
  Example res_exOrShareNested := [true; true; false].
  
  Example exShareNestedChoiceOr : Prog bool :=
    share ((pure true ? pure false) ? (pure true ? pure false)) >>= fun fx =>
      orM fx fx.
  Example res_exShareNestedChoiceOr := [true; false; true; false].
  
  Example exShareIgnoreShare : Prog bool :=
    share coin >>= fun fx =>
      const T (share fx >>= fun fy => orM fy fy).
  Example res_exShareIgnoreShare := [true].
  
  Example exRepeatedShare : Prog bool :=
    share coin >>= fun fx => share fx >>= fun fy => orM fy fy.
  Example res_exRepeatedShare := [true; false].

 Example exSkipIds : Prog bool :=
    Share coin >>= fun fx => const coin (const fx fx).
  Example res_exSkipIds := [true; false].
  
  Definition exBs :=
    [(example1, res_example1);
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
       (exRepeatedShare, res_exRepeatedShare);
       (exSkipIds, res_exSkipIds)].
  
  Lemma tests__exBs : Forall (fun '(p,r) => handle p = r) exBs.
  Proof. repeat econstructor. Qed.
End exB.


(** Examples for programs that return pairs of Boolean values *)
Section exPB.
  Example exDup : Prog (Pair bool bool) := dup coin.
  Example res_exDup := [Pair' T T
                        ; Pair' T F
                        ; Pair' F T
                        ; Pair' F F].
  
  Example exDupShare : Prog (Pair bool bool) := share coin >>= fun x => dup x.
  Example res_exDupShare := [Pair' T T; Pair' F F].
  
  Example exDupShare2 : Prog (Pair bool bool) := dupShare coin.

  Example res_exDupShare2 := [Pair' T T; Pair' F F].
  
  Example exDupFailed : Prog (Pair bool bool) := share Fail >>= fun x => dup (const T x).
  Example res_exDupFailed := [Pair' T T].
  
  Example exDupFirst : Prog (Pair bool bool) := dup (firstM (pairM coin (@Fail bool))).
  Example res_exDupFirst := [Pair' T T
                             ; Pair' T F
                             ; Pair' F T
                             ; Pair' F F].
  
  Example exDupShareFirst : Prog (Pair bool bool) := dupShare (@firstM bool bool (pairM coin Fail)).
  Example res_exDupShareFirst :=  [Pair' T T; Pair' F F].

  
  Example exShareNestedChoice : Prog (Pair bool bool) :=
    share ((pure true ? pure false) ? (pure true ? pure false)) >>= fun fx =>
      pairM fx fx.
  Example res_exShareNestedChoice := [Pair' T T 
                                      ; Pair' F F
                                      ; Pair' T T
                                      ; Pair' F F].
  
 
  Example exShareInShare : Prog (Pair bool bool) :=
    Share (Share coin >>= fun fx => orM fx fx) >>= fun fy => pairM fy fy.
  Example res_exShareInShare := [Pair' T T
                                 ; Pair' F F].

  Definition exPBs :=
    [(exDup, res_exDup)
     ; (exDupShare, res_exDupShare)
     ; (exDupShare2, res_exDupShare2)
     ; (exDupFailed, res_exDupFailed)
     ; (exDupFirst, res_exDupFirst)
     ; (exDupShareFirst, res_exDupShareFirst)
     ; (exShareNestedChoice, res_exShareNestedChoice)
     ; (exShareInShare, res_exShareInShare)].
  
  Lemma tests__exPBs : Forall (fun '(p,r) => handle p = r) exPBs.
  Proof. repeat econstructor. Qed.
End exPB.


(** Examples for programs that return lists of Boolean values *)
Section exLB.
  Arguments nilM {_}.
  Arguments Nil' {_}.

  Example exDupl : Prog (List bool) := dupl (headM (consM coin Fail)).
  Example res_exDupl := [Cons' T (consM T nilM)
                         ; Cons' T (consM F nilM)
                         ; Cons' F (consM T nilM)
                         ; Cons' F (consM F nilM)].

  Example exDupl2 : Prog (List bool) := consM (headM (consM coin Fail))
                                           (consM (headM (consM coin Fail)) nilM).
  Example res_exDupl2 := [Cons' T (consM T nilM)
                          ; Cons' T (consM F nilM)
                          ; Cons' F (consM T nilM)
                          ; Cons' F (consM F nilM)].

  Example exDuplShare : Prog (List bool) := duplShare (headM (consM coin Fail)).
  Example res_exDuplShare := [Cons' T (consM T nilM)
                              ; Cons' F (consM F nilM)].

  Example exShareNestedChoice2 : Prog (List bool) :=
    share (pure true ? (pure false ? pure true)) >>= fun fx =>
    share coin >>= fun fy =>
      consM fx (consM fy (consM fx (consM fy nilM))).

  Example res_exShareNestedChoice2 :=
    [Cons' T (consM T (consM T (consM T nilM)))
     ; Cons' T (consM F (consM T (consM F nilM)))
     ; Cons' F (consM T (consM F (consM T nilM)))
     ; Cons' F (consM F (consM F (consM F nilM)))
     ; Cons' T (consM T (consM T (consM T nilM)))
     ; Cons' T (consM F (consM T (consM F nilM)))].

  Example exOrShareNestedList : Prog (List bool) :=
    share coin >>= fun fx =>
    consM fx (share coin >>= fun fy =>
      consM fy (consM fx (consM fy nilM))).

  Example res_exOrShareNestedList :=
    [Cons' T (consM T (consM T (consM T nilM)))
     ; Cons' T (consM F (consM T (consM F nilM)))
     ; Cons' F (consM T (consM F (consM T nilM)))
     ; Cons' F (consM F (consM F (consM F nilM)))].

  Fixpoint recList' (xs : List bool) : Prog (List bool) :=
    match xs with
    | Nil' => nilM
    | Cons' fy fys => consM (notM fy)
                           (fys ? fys >>= fun zs => recList' zs)
    end.
  
  Definition recList (fxs : Prog (List bool)) : Prog (List bool) :=
    fxs >>= fun xs => recList' xs.
  
  Example exRecList : Prog (List bool) :=
    recList (consM T (consM F nilM)).
  Example res_exRecList :=  [(Cons' F (consM F nilM))
                             ; (Cons' F (consM T nilM))
                             ; (Cons' F (consM T nilM))].

  Example exSharePutPos : Prog (List bool) :=
    Share (Share (consM coin nilM) >>= fun fx => appM fx fx) >>= fun fy => appM fy fy.
  
  Example res_exSharePutPos := [Cons' T (consM T (consM T (consM T nilM)))
                                ; Cons'  F (consM F (consM F (consM F nilM)))].

  Example exShareListInRepeatedShare : Prog (List bool) :=
    Share (Share (consM coin nilM) >>= fun fx => appM fx fx) >>=
          fun fy => Share coin >>= fun fz => Share coin >>= fun fa => consM fz (consM fa fy).
  Example res_exShareListInRepeatedShare :=
    [Cons' T (consM T (consM T (consM T nilM)))
     ; Cons' T (consM T (consM F (consM F nilM)))
     ;  Cons' T (consM F (consM T (consM T nilM)))
     ;  Cons' T (consM F (consM F (consM F nilM)))
     ;  Cons' F (consM T (consM T (consM T nilM)))
     ;  Cons' F (consM T (consM F (consM F nilM)))
     ;  Cons' F (consM F (consM T (consM T nilM)))
     ;  Cons' F (consM F (consM F (consM F nilM)))].

  Definition exLBs :=
    [(exDupl, res_exDupl)
     ; (exDupl2,  res_exDupl2)
     ; (exDuplShare, res_exDuplShare)
     ; (exShareNestedChoice2, res_exShareNestedChoice2)
     ; (exOrShareNestedList, res_exOrShareNestedList)
     ; (exRecList, res_exRecList)
     ; (exSharePutPos, res_exSharePutPos)
     ; (exShareListInRepeatedShare, res_exShareListInRepeatedShare)].

  Lemma tests__exLBs : Forall (fun '(p,r) => handle p = r) exLBs.
  Proof. repeat econstructor. Qed.
End exLB.
              
(** Examples for programs that return lists of pairs of Boolean values *)
Section exLPB.
 Example exShareSingleton : Prog (Pair (List bool) (List bool)) :=
   Share (consM (pure true ? pure false) nilM) >>= fun fx =>
     pairM fx fx.
 Example res_exShareSingleton := [Pair' (pure (Cons' T nilM))
                                        (pure (Cons' T nilM))
                                  ; Pair' (pure (Cons' F nilM))
                                          (pure (Cons' F nilM))].

 
 Definition exLPBs := [(exShareSingleton, res_exShareSingleton)].
 
 Lemma tests__exLPBs : Forall (fun '(p,r) => handle p = r) exLPBs.
 Proof. repeat econstructor. Qed.
End exLPB.


(** Examples for programs that return pairs of lists of Boolean values *)
Section exPLB.
  Example exShareListInShare : Prog (Pair (List bool) (List bool)) :=
    Share (Share (consM coin (consM coin nilM)) >>=
                 fun fx => appM fx fx) >>= fun fy => pairM fy fy.
  
  Example res_exShareListInShare :=
    [Pair' (consM T (consM T (consM T (consM T nilM))))
           (consM T (consM T (consM T (consM T nilM))))
     ; Pair' (consM T (consM F (consM T (consM F nilM))))
             (consM T (consM F (consM T (consM F nilM))))
     ; Pair' (consM F (consM T (consM F (consM T nilM))))
             (consM F (consM T (consM F (consM T nilM))))
     ; Pair' (consM F (consM F (consM F (consM F nilM))))
             (consM F (consM F (consM F (consM F nilM))))].

  Definition exPLBs := [(exShareListInShare, res_exShareListInShare)].
 
 Lemma tests__exPLBs : Forall (fun '(p,r) => handle p = r) exPLBs.
 Proof. repeat econstructor. Qed.
End exPLB.