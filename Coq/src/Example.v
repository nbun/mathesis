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
Definition cons := Effect.cons.

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

Example exHead : Prog bool := headM (cons coin Fail).
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
(*
exOrShareNestedList :: (Sharing m, MonadPlus m) => m (List m Bool)
exOrShareNestedList = share coin >>= \fx ->
                  cons fx (share coin >>= \fy ->
                              cons fy (cons fx (cons fy nil)))

recList :: (Sharing m, MonadPlus m) => m (List m Bool) -> m (List m Bool)
recList fxs = fxs >>= \xfps -> case xfps of
                                    Nil -> nil
                                    Cons fy fys -> share fys >>= \fys' -> cons fy (fys' `mplus` recList fys')

exRecList :: (Sharing m, MonadPlus m) => m (Pair m (List m Bool))
exRecList = share (recList (cons (return True) (cons (return False) nil))) >>= \fx -> pairM fx fx

exRecListNested :: (Sharing m, MonadPlus m) => m (List m (List m Bool))
exRecListNested = share (recList (cons (return True) (cons (return False) nil)))
  >>= \fx -> cons fx (share (recList (cons (return True) (cons (return False) nil)))
                      >>= \fz -> cons fz (cons fx (cons fz nil)))
exSkipIds :: (Sharing m, MonadPlus m) => m Bool
exSkipIds = share coin >>= \fx -> const coin (const fx fx)
exLoop :: Sharing m => m Bool
exLoop = let loop :: m ()
             loop = loop in share loop >>= \fx -> const (return True) (const fx fx)
exLoop2 :: Sharing m => m Bool
exLoop2 = let loop :: m ()
              loop = loop in share loop >>= \fx -> const coin (const fx fx)

exDup :: (Sharing m, MonadPlus m) => m (Pair m Bool)
exDup = dup coin
exDupShare :: (Sharing m, MonadPlus m) => m (Pair m Bool)
exDupShare = share coin >>= dup
exDupShare2 :: (Sharing m, MonadPlus m) => m (Pair m Bool)
exDupShare2 = dupShare coin
exDupFailed :: (Sharing m, MonadPlus m) => m (Pair m Bool)
exDupFailed = share (mzero :: MonadPlus m => m Bool) >>= \x -> dup (const (return True) x)
exDupFirst :: MonadPlus m => m (Pair m Bool)
exDupFirst = dup (first (pairM coin mzero))
exDupShareFirst :: (Sharing m, MonadPlus m) => m (Pair m Bool)
exDupShareFirst = dupShare (first (pairM coin mzero))

exDupl :: MonadPlus m => m (List m Bool)
exDupl = dupl (headM (cons coin (mzero :: MonadPlus m => m (List m Bool))))
exDupl2 :: MonadPlus m => m (List m Bool)
exDupl2 = cons (headM (cons coin (mzero :: MonadPlus m => m (List m Bool))))
               (cons (headM (cons coin (mzero :: MonadPlus m => m (List m Bool))))
                     nil)
exDuplShare :: (Sharing m, MonadPlus m) => m (List m Bool)
exDuplShare = duplShare (headM (cons coin (mzero :: MonadPlus m => m (List m Bool))))

exShareNestedChoice :: (Sharing m, MonadPlus m) => m (Pair m Bool)
exShareNestedChoice =
  share (mplus (mplus (return True) (return False)) (mplus (return True) (return False))) >>=
    \fx -> pairM fx fx


exShareNestedChoice2 :: (Sharing m, MonadPlus m) => m (List m Bool)
exShareNestedChoice2 =
  share (mplus (return True) (mplus (return False) (return True))) >>=
    \fx -> share (mplus (return True) (return False)) >>= \fy -> cons fx (cons fy (cons fx (cons fy nil)))


exShareSingleton :: (Sharing m, MonadPlus m) => m (Pair m (List m Bool))
exShareSingleton =
  share (cons (return True `mplus` return False) nil) >>=
    \fx -> pairM fx fx

exShareInShare :: (Sharing m, MonadPlus m) => m (Pair m Bool)
exShareInShare = share (share coin >>= \fx -> orM fx fx) >>= \fy -> pairM fy fy

exShareListInShare :: (Sharing m, MonadPlus m) => m (Pair m (List m Bool))
exShareListInShare =
  share (share (cons coin (cons coin nil)) >>=
          \fx -> appM fx fx) >>= \fy -> pairM fy fy

exSharePutPos :: (Sharing m, MonadPlus m) =>  m (List m Bool)
exSharePutPos =
  share (share (cons coin nil) >>= \fx -> appM fx fx) >>= \fy -> appM fy fy

exShareListInRepeatedShare :: NDShare (List NDShare Bool)
exShareListInRepeatedShare =
  share (share (cons coin nil) >>= \fx -> appM fx fx) >>=
  \fy -> share coin >>= \fz -> share coin >>= \fa -> cons fz (cons fa fy)

tests = do
  let exBs  = [ (example1,"ex1",[True,False])
              , (example2,"ex2",[True,False,True,False])
              , (example3,"ex3",[True,False,True,False])
              , (exOr0,"exOr0",[True,False])
              , (exOr1,"exOr1",[True,True,False])
              , (exOr2,"exOr2",[True,False])
              , (exOr2a,"exOr2a",[True,False])
              , (exOr2b,"exOr2b",[True])
              , (exOr3,"exOr3",[True,True,True,True])
              , (exOr3a,"exOr3a",[True,True,False,True,True,False])
              , (exOr3b,"exOr3b",[True,True,False,True,False])
              , (exOr3c,"exOr3c",[True,True,False,True,False,True,True,False,True,False])
              , (exOr4,"exOr4",[True,True,False])
              , (exOrShare,"exOrShare",[True,True,False])
              , (exOr6,"exOr6",[True,True,False])
              , (exOr7,"exOr7",[True,True,False])
              , (exOr7a,"exOr7a",[True])
              , (exOr7b,"exOr7b",[True,False])
              , (exShareConst,"exShareConst",[True,False])
              , (exShareConstOrR,"exShareConstOrR",[True,False])
              , (exShareConstOrL,"exShareConstOrL",[True,False])
              , (exShareConstOrR2,"exShareConstOrR2",[True])
              , (exFailed,"exFailed",[True])
              , (exHead,"exHead", [ True, False ])
              , (exOrShareShare,"exOrShareShare", [True,True,False])
              , (exOrShareNested,"exOrShareNested", [True,True,False])
              , (exShareNestedChoiceOr, "exShareNestedChoiceOr", [True,False,True,False])
              , (exShareIgnoreShare, "exShareIgnoreShare", [True])
              , (exRepeatedShare, "exRepeatedShare", [True,False])
              ]
      exPBs = [ (exDup,"exDup",[ Pair (Identity True) (Identity True)
                               , Pair (Identity True) (Identity False)
                               , Pair (Identity False) (Identity True)
                               , Pair (Identity False) (Identity False)
                               ])
              , (exDupShare,"exDupShare",[ Pair (Identity True) (Identity True)
                                         , Pair (Identity False) (Identity False)
                                         ])
              , (exDupShare2,"exDupShare2",[ Pair (Identity True) (Identity True)
                                           , Pair (Identity False) (Identity False)
                                           ])
              , (exDupFailed,"exDupFailed",[ Pair (Identity True) (Identity True) ])
              , (exDupFirst,"exDupFirst",[ Pair (Identity True) (Identity True)
                                         , Pair (Identity True) (Identity False)
                                         , Pair (Identity False) (Identity True)
                                         , Pair (Identity False) (Identity False)
                                         ])
              , (exDupShareFirst,"exShareDupFirst", [ Pair (Identity True) (Identity True)
                                                    , Pair (Identity False) (Identity False)
                                                    ])
              , (exDupShare2,"exDupShare2",[ Pair (Identity True) (Identity True)
                                           , Pair (Identity False) (Identity False)
                                           ])
              , (exShareNestedChoice, "exShareNestedChoice",
                               [ Pair (Identity True) (Identity True)
                               , Pair (Identity False) (Identity False)
                               , Pair (Identity True) (Identity True)
                               , Pair (Identity False) (Identity False)
                               ])
              ]
      exLBs = [ (exDupl,"exDupl", [ Cons (Identity True) (cons (Identity True) nil)
                                    , Cons (Identity True) (cons (Identity False) nil)
                                    , Cons (Identity False) (cons (Identity True) nil)
                                    , Cons (Identity False) (cons (Identity False) nil)
                                    ])
              , (exDuplShare,"exDuplShare", [ Cons (Identity True) (cons (Identity True) nil)
                                            , Cons (Identity False) (cons (Identity False) nil)
                                            ])
              , (exDupl2,"exDupl2", [ Cons (Identity True) (cons (Identity True) nil)
                                    , Cons (Identity True) (cons (Identity False) nil)
                                    , Cons (Identity False) (cons (Identity True) nil)
                                    , Cons (Identity False) (cons (Identity False) nil)
                                    ])
              , (exShareNestedChoice2, "exShareNestedChoice2",
                  [ Cons (Identity True) (cons (Identity True) (cons (Identity True) (cons (Identity True) nil)))
                  , Cons (Identity True) (cons (Identity False) (cons (Identity True) (cons (Identity False) nil)))
                  , Cons (Identity False) (cons (Identity True) (cons (Identity False) (cons (Identity True) nil)))
                  , Cons (Identity False) (cons (Identity False) (cons (Identity False) (cons (Identity False) nil)))
                  , Cons (Identity True) (cons (Identity True) (cons (Identity True) (cons (Identity True) nil)))
                  , Cons (Identity True) (cons (Identity False) (cons (Identity True) (cons (Identity False) nil)))
                  ])
              , (exOrShareNestedList, "exOrShareNestedList",
                 [ Cons (Identity True) (cons (Identity True) (cons (Identity True) (cons (Identity True) nil)))
                 , Cons (Identity True) (cons (Identity False) (cons (Identity True) (cons (Identity False) nil)))
                 , Cons (Identity False) (cons (Identity True) (cons (Identity False) (cons (Identity True) nil)))
                 , Cons (Identity False) (cons (Identity False) (cons (Identity False) (cons (Identity False) nil)))
                 ])
              ]
      exLPBs = [ (exShareSingleton, "exShareSingleton", [ Pair (Identity (Cons (Identity True) nil))
                                                               (Identity (Cons (Identity True) nil))
                                                        , Pair (Identity (Cons (Identity False) nil))
                                                               (Identity (Cons (Identity False) nil))
                                                        ])
               , (exRecList, "exRecList", [ Pair (cons (Identity True) (cons (Identity False) nil))
                                                (cons (Identity True) (cons (Identity False) nil))
                                          , Pair (cons (Identity True) (cons (Identity False) nil))
                                                 (cons (Identity True) (cons (Identity False) nil))
                                          , Pair (cons (Identity True) (cons (Identity False) nil))
                                                (cons (Identity True) (cons (Identity False) nil))
                                          ])
               ]
      maxName = maximum (map (\(_,name,_) -> length name) exBs ++
                         map (\(_,name,_) -> length name) exPBs ++
                         map (\(_,name,_) -> length name) exLBs)
      prettyName name = name ++ ": " ++ replicate (maxName - length name) ' '

  -- Based on the imported implementation, the annotations for `e` might have to be adapted!
  mapM_ (\(e,name,v) -> putStr (prettyName name) >> pprint (collectVals (e :: NDShare Bool) == v)) exBs
  mapM_ (\(e,name,v) -> putStr (prettyName name) >> pprint (collectVals (e :: NDShare (Pair NDShare Bool)) == v)) exPBs
  mapM_ (\(e,name,v) -> putStr (prettyName name) >> pprint (collectVals (e :: NDShare (List NDShare Bool)) == v)) exLBs
  mapM_ (\(e,name,v) -> putStr (prettyName name) >>
    pprint (collectVals (e :: NDShare (Pair NDShare (List NDShare Bool))) == v)) exLPBs

*)
