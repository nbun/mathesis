Require Import Thesis.HigherOrder.DataM.
Require Import Thesis.HigherOrder.Effect.
Require Import Thesis.HigherOrder.Handler.
Require Import Thesis.HigherOrder.Prog.

Require Import Lists.List.

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
  Example res_example3 := [true; false; true; false].
  
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
  
  Example exDupFirst : Prog (Pair bool bool) := dup (firstM (pairM coin (@Fail bool))).
  Example res_exDupFirst := [Pair' (pure true) (pure true)
                             ; Pair' (pure true) (pure false)
                             ; Pair' (pure false) (pure true)
                             ; Pair' (pure false) (pure false)].
  
  Example exDupShareFirst : Prog (Pair bool bool) := dupShare (@firstM bool bool (pairM coin Fail)).
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
End Extra.