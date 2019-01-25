module TestSharing where
import Control.Findall (allValues)
import List (maximum)

coin :: Bool
coin = True ? False

example1 :: Bool
example1 = coin
example2 :: Bool
example2 = coin ? coin
example3 :: Bool
example3 = let x = coin in x ? x

exOr0 :: Bool
exOr0 = coin || False
exOr1 :: Bool
exOr1 = coin || coin
exOr2 :: Bool
exOr2 = let x = coin in x || x
exOr2a :: Bool
exOr2a = let x = coin in False || (x || x)
exOr2b :: Bool
exOr2b = let x = coin in True || (x || x)

exOr3 :: Bool
exOr3 = (coin ? coin) || True
exOr3a :: Bool
exOr3a = (coin ? coin) || coin
exOr3b :: Bool
exOr3b = coin || (coin ? coin)
exOr3c :: Bool
exOr3c = (coin ? coin) || (coin ? coin)
exOr4 :: Bool
exOr4 = let x = coin in x || coin
exOrShare :: Bool
exOrShare = let x = coin in coin || x

exOr6 :: Bool
exOr6 = let x = coin in x || (x || coin)
exOr7 :: Bool
exOr7 = let x = coin in coin || (x || x)
exOr7a :: Bool
exOr7a = let x = coin in True || (x || x)
exOr7b :: Bool
exOr7b = let x = coin in False || (x || x)
exShareConst :: Bool
exShareConst = let x = coin in const x x
exShareConstOrR :: Bool
exShareConstOrR = let x = coin in x || (const x x)
exShareConstOrL :: Bool
exShareConstOrL = let x = coin in (const x x) || x
exShareConstOrR2 :: Bool
exShareConstOrR2 = let x = coin in True || (const x x)
exOrShareShare :: Bool
exOrShareShare = let x = coin
                     y = coin
                 in x || (y || (x || y))
exOrShareNested :: Bool
exOrShareNested = let x = coin
                  in x || (let y = coin in y || (x || y))

exOrShareNestedList :: [Bool]
exOrShareNestedList = let x = coin
                      in x : (let y = coin in y : x : [y])

recList :: [Bool] -> [Bool]
recList xs = case xs of
               []     -> []
               y : ys -> let ys' = ys in y : (ys' ? recList ys')

exRecList :: ([Bool], [Bool])
exRecList = let xs = recList [True, False] in (xs, xs)

exRecListNested :: [[Bool]]
exRecListNested = let xs = recList [True, False]
                  in xs : (let ys = recList [True, False] in ys : xs : [ys])

exFailed ::  Bool
exFailed = let x = failed in const True x
exSkipIds :: Bool
exSkipIds = let x = coin in const coin (const x x)
exLoop :: Bool
exLoop = let loop = loop in let x = loop in const True (const x x)
exLoop2 :: Bool
exLoop2 = let loop = loop in let x = loop in const coin (const x x)
exHead :: Bool
exHead = head (coin : failed)
exRepeatedShare :: Bool
exRepeatedShare = let x = coin
                      y = x
                  in y || y
exShareIgnoreShare :: Bool
exShareIgnoreShare = let x = coin in const True (let y = x in y || y)

dup :: a -> (a, a)
dup x = (x,x)

dupShare :: a -> (a, a)
dupShare x = let y = x in (y,y)

exDup :: (Bool, Bool)
exDup = dup coin
exDupShare :: (Bool, Bool)
exDupShare = let x = coin in dup x
exDupShare2 :: (Bool, Bool)
exDupShare2 = dupShare coin
exDupFailed :: (Bool, Bool)
exDupFailed = let x = failed in dup (const True x)
exDupFirst :: (Bool, Bool)
exDupFirst = dup (fst (coin, failed))
exDupShareFirst :: (Bool, Bool)
exDupShareFirst = dupShare (fst (coin, failed))

dupl :: a -> [a]
dupl x = [x, x]

duplShare :: a -> [a]
duplShare x = let y = x in [y, y]

exDupl :: [Bool]
exDupl = dupl (head (coin : failed))
exDupl2 :: [Bool]
exDupl2 =  (head (coin : failed )) : [head (coin : failed)]
exDuplShare :: [Bool]
exDuplShare = duplShare (head (coin : failed))

exShareNestedChoice :: (Bool, Bool)
exShareNestedChoice = let x = (True ? False) ? (True ? False) in (x,x)

exShareNestedChoice2 :: [Bool]
exShareNestedChoice2 = let x = True ? (False ? True)
                           y = True ? False
                       in [x, y, x, y]

exShareNestedChoiceOr :: Bool
exShareNestedChoiceOr = let x = ((True ? False) ? (True ? False)) in x || x

exShareSingleton :: ([Bool], [Bool])
exShareSingleton = let x = [True ? False] in (x,x)

exShareInShare :: (Bool, Bool)
exShareInShare = let y = let x = coin in x || x in (y,y)

exShareListInShare :: ([Bool], [Bool])
exShareListInShare = let ys = let xs = [coin, coin] in xs ++ xs in (ys,ys)

exSharePutPos :: [Bool]
exSharePutPos = let ys = let xs = [coin] in xs ++ xs in ys ++ ys

exShareListInRepeatedShare :: [Bool]
exShareListInRepeatedShare = let ys = let xs = [coin] in xs ++ xs
                             in let x = coin
                                    y = coin
                                in x : y : ys

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
      exPBs = [ (exDup,"exDup",[ (True,True)
                               , (True,False)
                               , (False,True)
                               , (False,False)
                               ])
              , (exDupShare,"exDupShare",[ (True,True)
                                         , (False,False)
                                         ])
              , (exDupShare2,"exDupShare2",[ (True,True)
                                           , (False,False)
                                           ])
              , (exDupFailed,"exDupFailed",[(True,True)])
              , (exDupFirst,"exDupFirst",[ (True,True)
                                         , (True,False)
                                         , (False,True)
                                         , (False,False)
                                         ])
              , (exDupShareFirst,"exShareDupFirst", [ (True,True)
                                                    , (False,False)
                                                    ])
              , (exDupShare2,"exDupShare2",[ (True,True)
                                           , (False,False)
                                           ])
              , (exShareNestedChoice, "exShareNestedChoice",
                               [ (True,True)
                               , (False,False)
                               , (True,True)
                               , (False,False)
                               ])
              ]
      exLBs = [ (exDupl,"exDupl", [ [True, True]
                                    , [True, False]
                                    , [False, True]
                                    , [False, False]
                                    ])
              , (exDuplShare,"exDuplShare", [ [True,True]
                                            , [False,False]
                                            ])
              , (exDupl2,"exDupl2", [ [True,True]
                                    , [True,False]
                                    , [False,True]
                                    , [False,False]
                                    ])
              , (exShareNestedChoice2, "exShareNestedChoice2",
                  [ [True,True,True,True]
                  , [True,False,True,False]
                  , [False,True,False,True]
                  , [False,False,False,False]
                  , [True,True,True,True]
                  , [True,False,True,False]
                  ])
              , (exOrShareNestedList, "exOrShareNestedList",
                 [ [True,True,True,True]
                 , [True,False,True,False]
                 , [False,True,False,True]
                 , [False,False,False,False]
                 ])
              ]
      exLPBs = [ (exShareSingleton, "exShareSingleton", [ ([True], [True])
                                                        , ([False], [False])
                                                        ])
               , (exRecList, "exRecList", [ ([True,False], [True,False])
                                          , ([True,False], [True,False])
                                          , ([True,False], [True,False])
                                          ])
               ]
      maxName = maximum (map (\(_,name,_) -> length name) exBs ++
                         map (\(_,name,_) -> length name) exPBs ++
                         map (\(_,name,_) -> length name) exLBs)
      prettyName name = name ++ ": " ++ replicate (maxName - length name) ' '

  mapM_ (\(e,name,v) -> putStr (prettyName name) >> print (allValues e == v)) exBs
  mapM_ (\(e,name,v) -> putStr (prettyName name) >> print (allValues e == v)) exPBs
  mapM_ (\(e,name,v) -> putStr (prettyName name) >> print (allValues e == v)) exLBs
  mapM_ (\(e,name,v) -> putStr (prettyName name) >> print (allValues e == v)) exLPBs
