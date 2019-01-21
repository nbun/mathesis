Require Import Thesis.Handler.
Require Import Thesis.Effect.
Require Import Thesis.Free.
Require Import Thesis.Base.
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

Arguments nilM {_}.

Example exOrShareNestedList : Prog (List bool) :=
  share coin >>= fun fx =>
                   consM fx (share coin >>= fun fy =>
                                             consM fy (consM fx (consM fy nilM))).
(*
recList :: (Sharing m, MonadPlus m) => m (List m Bool) => m (List m Bool)
recList fxs = fxs >>= fun xfps => case xfps of
                                    Nil' => nil
                                    Cons' fy fys => share fys >>= fun fys' => consM fy (fys' `mplus` recList fys')

exRecList :: (Sharing m, MonadPlus m) => m (Pair m (List m Bool))
exRecList = share (recList (consM (pure true) (consM (pure false) nil))) >>= fun fx => pairM fx fx

exRecListNested :: (Sharing m, MonadPlus m) => m (List m (List m Bool))
exRecListNested = share (recList (consM (pure true) (consM (pure false) nil)))
  >>= fun fx => consM fx (share (recList (consM (pure true) (consM (pure false) nil)))
                      >>= fun fz => consM fz (consM fx (consM fz nil)))
exSkipIds :: (Sharing m, MonadPlus m) => m Bool
exSkipIds = share coin >>= fun fx => const coin (const fx fx)
exLoop :: Sharing m => m Bool
exLoop = let loop :: m ()
             loop = loop in share loop >>= fun fx => const (pure true) (const fx fx)
exLoop2 :: Sharing m => m Bool
exLoop2 = let loop :: m ()
              loop = loop in share loop >>= fun fx => const coin (const fx fx)

exDupl :: MonadPlus m => m (List m Bool)
exDupl = dupl (headM (consM coin (mzero :: MonadPlus m => m (List m Bool))))
exDupl2 :: MonadPlus m => m (List m Bool)
exDupl2 = consM (headM (consM coin (mzero :: MonadPlus m => m (List m Bool))))
               (consM (headM (consM coin (mzero :: MonadPlus m => m (List m Bool))))
                     nil)
exDuplShare :: (Sharing m, MonadPlus m) => m (List m Bool)
exDuplShare = duplShare (headM (consM coin (mzero :: MonadPlus m => m (List m Bool))))

exShareNestedChoice2 :: (Sharing m, MonadPlus m) => m (List m Bool)
exShareNestedChoice2 =
  share (mplus (pure true) (mplus (pure false) (pure true))) >>=
    fun fx => share (mplus (pure true) (pure false)) >>= fun fy => consM fx (consM fy (consM fx (consM fy nil)))


exShareSingleton :: (Sharing m, MonadPlus m) => m (Pair m (List m Bool))
exShareSingleton =
  share (consM (pure true `mplus` pure false) nil) >>=
    fun fx => pairM fx fx

exShareInShare :: (Sharing m, MonadPlus m) => m (Pair m Bool)
exShareInShare = share (share coin >>= fun fx => orM fx fx) >>= fun fy => pairM fy fy

exShareListInShare :: (Sharing m, MonadPlus m) => m (Pair m (List m Bool))
exShareListInShare =
  share (share (consM coin (consM coin nil)) >>=
          fun fx => appM fx fx) >>= fun fy => pairM fy fy

exSharePutPos :: (Sharing m, MonadPlus m) =>  m (List m Bool)
exSharePutPos =
  share (share (consM coin nil) >>= fun fx => appM fx fx) >>= fun fy => appM fy fy

exShareListInRepeatedShare :: NDShare (List NDShare Bool)
exShareListInRepeatedShare =
  share (share (consM coin nil) >>= fun fx => appM fx fx) >>=
  fun fy => share coin >>= fun fz => share coin >>= fun fa => consM fz (consM fa fy)

tests = do
  let exBs  = [ (example1,"ex1",[true,false])
              , (example2,"ex2",[true,false,true,false])
              , (example3,"ex3",[true,false,true,false])
              , (exOr0,"exOr0",[true,false])
              , (exOr1,"exOr1",[true,true,false])
              , (exOr2,"exOr2",[true,false])
              , (exOr2a,"exOr2a",[true,false])
              , (exOr2b,"exOr2b",[true])
              , (exOr3,"exOr3",[true,true,true,true])
              , (exOr3a,"exOr3a",[true,true,false,true,true,false])
              , (exOr3b,"exOr3b",[true,true,false,true,false])
              , (exOr3c,"exOr3c",[true,true,false,true,false,true,true,false,true,false])
              , (exOr4,"exOr4",[true,true,false])
              , (exOrShare,"exOrShare",[true,true,false])
              , (exOr6,"exOr6",[true,true,false])
              , (exOr7,"exOr7",[true,true,false])
              , (exOr7a,"exOr7a",[true])
              , (exOr7b,"exOr7b",[true,false])
              , (exShareConst,"exShareConst",[true,false])
              , (exShareConstOrR,"exShareConstOrR",[true,false])
              , (exShareConstOrL,"exShareConstOrL",[true,false])
              , (exShareConstOrR2,"exShareConstOrR2",[true])
              , (exFailed,"exFailed",[true])
              , (exHead,"exHead", [ true, false ])
              , (exOrShareShare,"exOrShareShare", [true,true,false])
              , (exOrShareNested,"exOrShareNested", [true,true,false])
              , (exShareNestedChoiceOr, "exShareNestedChoiceOr", [true,false,true,false])
              , (exShareIgnoreShare, "exShareIgnoreShare", [true])
              , (exRepeatedShare, "exRepeatedShare", [true,false])
              ]
      exPBs = [ (exDup,"exDup",[ Pair (Identity true) (Identity true)
                               , Pair (Identity true) (Identity false)
                               , Pair (Identity false) (Identity true)
                               , Pair (Identity false) (Identity false)
                               ])
              , (exDupShare,"exDupShare",[ Pair (Identity true) (Identity true)
                                         , Pair (Identity false) (Identity false)
                                         ])
              , (exDupShare2,"exDupShare2",[ Pair (Identity true) (Identity true)
                                           , Pair (Identity false) (Identity false)
                                           ])
              , (exDupFailed,"exDupFailed",[ Pair (Identity true) (Identity true) ])
              , (exDupFirst,"exDupFirst",[ Pair (Identity true) (Identity true)
                                         , Pair (Identity true) (Identity false)
                                         , Pair (Identity false) (Identity true)
                                         , Pair (Identity false) (Identity false)
                                         ])
              , (exDupShareFirst,"exShareDupFirst", [ Pair (Identity true) (Identity true)
                                                    , Pair (Identity false) (Identity false)
                                                    ])
              , (exDupShare2,"exDupShare2",[ Pair (Identity true) (Identity true)
                                           , Pair (Identity false) (Identity false)
                                           ])
              , (exShareNestedChoice, "exShareNestedChoice",
                               [ Pair (Identity true) (Identity true)
                               , Pair (Identity false) (Identity false)
                               , Pair (Identity true) (Identity true)
                               , Pair (Identity false) (Identity false)
                               ])
              ]
      exLBs = [ (exDupl,"exDupl", [ ConsM (Identity true) (consM (Identity true) nil)
                                    , ConsM (Identity true) (consM (Identity false) nil)
                                    , ConsM (Identity false) (consM (Identity true) nil)
                                    , ConsM (Identity false) (consM (Identity false) nil)
                                    ])
              , (exDuplShare,"exDuplShare", [ ConsM (Identity true) (consM (Identity true) nil)
                                            , ConsM (Identity false) (consM (Identity false) nil)
                                            ])
              , (exDupl2,"exDupl2", [ ConsM (Identity true) (consM (Identity true) nil)
                                    , ConsM (Identity true) (consM (Identity false) nil)
                                    , ConsM (Identity false) (consM (Identity true) nil)
                                    , ConsM (Identity false) (consM (Identity false) nil)
                                    ])
              , (exShareNestedChoice2, "exShareNestedChoice2",
                  [ ConsM (Identity true) (consM (Identity true) (consM (Identity true) (consM (Identity true) nil)))
                  , ConsM (Identity true) (consM (Identity false) (consM (Identity true) (consM (Identity false) nil)))
                  , ConsM (Identity false) (consM (Identity true) (consM (Identity false) (consM (Identity true) nil)))
                  , ConsM (Identity false) (consM (Identity false) (consM (Identity false) (consM (Identity false) nil)))
                  , ConsM (Identity true) (consM (Identity true) (consM (Identity true) (consM (Identity true) nil)))
                  , ConsM (Identity true) (consM (Identity false) (consM (Identity true) (consM (Identity false) nil)))
                  ])
              , (exOrShareNestedList, "exOrShareNestedList",
                 [ ConsM (Identity true) (consM (Identity true) (consM (Identity true) (consM (Identity true) nil)))
                 , ConsM (Identity true) (consM (Identity false) (consM (Identity true) (consM (Identity false) nil)))
                 , ConsM (Identity false) (consM (Identity true) (consM (Identity false) (consM (Identity true) nil)))
                 , ConsM (Identity false) (consM (Identity false) (consM (Identity false) (consM (Identity false) nil)))
                 ])
              ]
      exLPBs = [ (exShareSingleton, "exShareSingleton", [ Pair (Identity (ConsM (Identity true) nil))
                                                               (Identity (ConsM (Identity true) nil))
                                                        , Pair (Identity (ConsM (Identity false) nil))
                                                               (Identity (ConsM (Identity false) nil))
                                                        ])
               , (exRecList, "exRecList", [ Pair (consM (Identity true) (consM (Identity false) nil))
                                                (consM (Identity true) (consM (Identity false) nil))
                                          , Pair (consM (Identity true) (consM (Identity false) nil))
                                                 (consM (Identity true) (consM (Identity false) nil))
                                          , Pair (consM (Identity true) (consM (Identity false) nil))
                                                (consM (Identity true) (consM (Identity false) nil))
                                          ])
               ]
      maxName = maximum (map (fun (_,name,_) => length name) exBs ++
                         map (fun (_,name,_) => length name) exPBs ++
                         map (fun (_,name,_) => length name) exLBs)
      prettyName name = name ++ ": " ++ replicate (maxName - length name) ' '

  -- Based on the imported implementation, the annotations for `e` might have to be adapted!
  mapM_ (fun (e,name,v) => putStr (prettyName name) >> pprint (collectVals (e :: NDShare Bool) == v)) exBs
  mapM_ (fun (e,name,v) => putStr (prettyName name) >> pprint (collectVals (e :: NDShare (Pair NDShare Bool)) == v)) exPBs
  mapM_ (fun (e,name,v) => putStr (prettyName name) >> pprint (collectVals (e :: NDShare (List NDShare Bool)) == v)) exLBs
  mapM_ (fun (e,name,v) => putStr (prettyName name) >>
    pprint (collectVals (e :: NDShare (Pair NDShare (List NDShare Bool))) == v)) exLPBs
