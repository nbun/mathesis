{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeOperators       #-}

module TestSharing where

import           Base
import           Control.Monad         (MonadPlus (..))
import           Data.Functor.Identity (Identity (..))
import           Debug.Trace
import           Pretty                (pprint)
import           SharingInterface

import           Data.ListM
import           Data.PairM
import           Data.PrimM

-- import whatever implementation you like to test
import           CallTimeChoice

example1 :: MonadPlus m => m Bool
example1 = coin
example2 :: MonadPlus m => m Bool
example2 = mplus coin coin
example3 :: (Sharing m, MonadPlus m) => m Bool
example3 = share coin >>= \fx -> mplus fx fx

exOr0 :: MonadPlus m => m Bool
exOr0 = orM coin (return False)
exOr1 :: MonadPlus m => m Bool
exOr1 = orM coin coin
exOr2 :: (Sharing m, MonadPlus m) => m Bool
exOr2 = share coin >>= \fx -> orM fx fx
exOr2a :: (Sharing m, MonadPlus m) => m Bool
exOr2a = share coin >>= \fx -> orM (return False) (orM fx fx)
exOr2b :: (Sharing m, MonadPlus m) => m Bool
exOr2b = share coin >>= \fx -> orM (return True) (orM fx fx)

exOr3 :: MonadPlus m => m Bool
exOr3 = orM (mplus coin coin) (return True)
exOr3a :: MonadPlus m => m Bool
exOr3a = orM (mplus coin coin) coin
exOr3b :: MonadPlus m => m Bool
exOr3b = orM coin (mplus coin coin)
exOr3c :: MonadPlus m => m Bool
exOr3c = orM (mplus coin coin) (mplus coin coin)
-- here we share, even though nothing is shared
exOr4 :: (Sharing m, MonadPlus m) => m Bool
exOr4 = share coin >>= \fx -> orM fx coin
exOrShare :: (Sharing m, MonadPlus m) => m Bool
exOrShare = share coin >>= \fx -> orM coin fx
--
exOr6 :: (Sharing m, MonadPlus m) => m Bool
exOr6 = share coin >>= \fx -> orM fx (orM fx coin)
exOr7 :: (Sharing m, MonadPlus m) => m Bool
exOr7 = share coin >>= \fx -> orM coin (orM fx fx)
exOr7a :: (Sharing m, MonadPlus m) => m Bool
exOr7a = share coin >>= \fx -> orM (return True) (orM fx fx)
exOr7b :: (Sharing m, MonadPlus m) => m Bool
exOr7b = share coin >>= \fx -> orM (return False) (orM fx fx)
exShareConst :: (Sharing m, MonadPlus m) => m Bool
exShareConst = share coin >>= \fx -> const fx fx
exShareConstOrR :: (Sharing m, MonadPlus m) => m Bool
exShareConstOrR = share coin >>= \fx -> orM fx (const fx fx)
exShareConstOrL :: (Sharing m, MonadPlus m) => m Bool
exShareConstOrL = share coin >>= \fx -> orM (const fx fx) fx
exShareConstOrR2 :: (Sharing m, MonadPlus m) => m Bool
exShareConstOrR2 = share coin >>= \fx -> orM (return True) (const fx fx)
exOrShareShare :: (Sharing m, MonadPlus m) => m Bool
exOrShareShare = share coin >>= \fx ->
                 share coin >>= \fy ->
                 orM fx (orM fy (orM fx fy))
exOrShareNested :: (Sharing m, MonadPlus m) => m Bool
exOrShareNested = share coin >>= \fx ->
                  orM fx (share coin >>= \fy ->
                              orM fy (orM fx fy))

exOrShareNestedList :: (Sharing m, MonadPlus m) => m (List m Bool)
exOrShareNestedList = share coin >>= \fx ->
                  cons fx (share coin >>= \fy ->
                              cons fy (cons fx (cons fy nil)))

recList :: (Sharing m, MonadPlus m) => m (List m Bool) -> m (List m Bool)
recList fxs = fxs >>= \xfps -> case xfps of
                                    Nil -> nil
                                    Cons fy fys -> share fys >>= \fys' ->
                                      cons (notM fy) (fys' `mplus` recList fys')

exRecList :: (Sharing m, MonadPlus m) => m (List m Bool)
exRecList = recList (cons (return True) (cons (return False) nil))

exFailed :: (Sharing m, MonadPlus m) => m Bool
exFailed = share (mzero :: MonadPlus m => m Bool) >>= \fx -> const (return True) fx
exSkipIds :: (Sharing m, MonadPlus m) => m Bool
exSkipIds = share coin >>= \fx -> const coin (const fx fx)
exLoop :: Sharing m => m Bool
exLoop = let loop :: m ()
             loop = loop in share loop >>= \fx -> const (return True) (const fx fx)
exLoop2 :: Sharing m => m Bool
exLoop2 = let loop :: m ()
              loop = loop in share loop >>= \fx -> const coin (const fx fx)
exHead :: (Sharing m, MonadPlus m) => m Bool
exHead = headM (cons coin (mzero :: MonadPlus m => m (List m Bool)))
exRepeatedShare :: (Sharing m, MonadPlus m) => m Bool
exRepeatedShare = share coin >>= \fx -> share fx >>= \fy -> orM fy fy
exShareIgnoreShare :: (Sharing m, MonadPlus m) => m Bool
exShareIgnoreShare =
  share coin >>= \fx -> const (return True) (share fx >>= \fy -> orM fy fy)

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

exShareNestedChoiceOr :: (Sharing m, MonadPlus m) => m Bool
exShareNestedChoiceOr =
  share (mplus (mplus (return True) (return False)) (mplus (return True) (return False))) >>=
    \fx -> orM fx fx

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

t :: Identity Bool
t = Identity True

f :: Identity Bool
f = Identity False

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
      exPBs = [ (exDup,"exDup",[ Pair t t
                               , Pair t f
                               , Pair f t
                               , Pair f f
                               ])
              , (exDupShare,"exDupShare",[ Pair t t
                                         , Pair f f
                                         ])
              , (exDupShare2,"exDupShare2",[ Pair t t
                                           , Pair f f
                                           ])
              , (exDupFailed,"exDupFailed",[ Pair t t ])
              , (exDupFirst,"exDupFirst",[ Pair t t
                                         , Pair t f
                                         , Pair f t
                                         , Pair f f
                                         ])
              , (exDupShareFirst,"exShareDupFirst", [ Pair t t
                                                    , Pair f f
                                                    ])
              , (exDupShare2,"exDupShare2",[ Pair t t
                                           , Pair f f
                                           ])
              , (exShareNestedChoice, "exShareNestedChoice", [ Pair t t
                                                             , Pair f f
                                                             , Pair t t
                                                             , Pair f f
                                                             ])
              , (exShareInShare, "exShareInShare", [ Pair t t
                                                   , Pair f f ])
              ]
      exLBs = [ (exDupl,"exDupl", [ Cons t (cons t nil)
                                  , Cons t (cons f nil)
                                  , Cons f (cons t nil)
                                  , Cons f (cons f nil)
                                  ])
              , (exDuplShare,"exDuplShare", [ Cons t (cons t nil)
                                            , Cons f (cons f nil)
                                            ])
              , (exDupl2,"exDupl2", [ Cons t (cons t nil)
                                    , Cons t (cons f nil)
                                    , Cons f (cons t nil)
                                    , Cons f (cons f nil)
                                    ])
              , (exShareNestedChoice2, "exShareNestedChoice2",
                  [ Cons t (cons t (cons t (cons t nil)))
                  , Cons t (cons f (cons t (cons f nil)))
                  , Cons f (cons t (cons f (cons t nil)))
                  , Cons f (cons f (cons f (cons f nil)))
                  , Cons t (cons t (cons t (cons t nil)))
                  , Cons t (cons f (cons t (cons f nil)))
                  ])
              , (exOrShareNestedList, "exOrShareNestedList",
                 [ Cons t (cons t (cons t (cons t nil)))
                 , Cons t (cons f (cons t (cons f nil)))
                 , Cons f (cons t (cons f (cons t nil)))
                 , Cons f (cons f (cons f (cons f nil)))
                 ])
              , (exRecList, "exRecList", [ Cons f (cons f nil)
                                         , Cons f (cons t nil)
                                         , Cons f (cons t nil)
                                          ])
              , (exSharePutPos, "exSharePutPos",
                 [ Cons t (cons t (cons t (cons t nil)))
                 , Cons f (cons f (cons f (cons f nil)))
                 ])
              , (exShareListInRepeatedShare, "exShareListInRepeatedShare",
                  [ Cons t (cons t (cons t (cons t nil)))
                  , Cons t (cons t (cons f (cons f nil)))
                  , Cons t (cons f (cons t (cons t nil)))
                  , Cons t (cons f (cons f (cons f nil)))
                  , Cons f (cons t (cons t (cons t nil)))
                  , Cons f (cons t (cons f (cons f nil)))
                  , Cons f (cons f (cons t (cons t nil)))
                  , Cons f (cons f (cons f (cons f nil)))])
              ]
      exLPBs = [ (exShareSingleton, "exShareSingleton",
                   [ Pair (Identity (Cons t nil))
                     (Identity (Cons t nil))
                   , Pair (Identity (Cons f nil))
                     (Identity (Cons f nil))
                   ])
               , (exShareListInShare, "exShareListInShare",
                  [ Pair (cons t (cons t (cons t (cons t nil))))
                         (cons t (cons t (cons t (cons t nil))))
                  , Pair (cons t (cons f (cons t (cons f nil))))
                         (cons t (cons f (cons t (cons f nil))))
                  , Pair (cons f (cons t (cons f (cons t nil))))
                         (cons f (cons t (cons f (cons t nil))))
                  , Pair (cons f (cons f (cons f (cons f nil))))
                         (cons f (cons f (cons f (cons f nil))))
                  ])

               ]
      maxName = maximum (map (\(_,name,_) -> length name) exBs ++
                         map (\(_,name,_) -> length name) exPBs ++
                         map (\(_,name,_) -> length name) exLBs)
      prettyName name = name ++ ": " ++ replicate (maxName - length name) ' '

  -- Based on the imported implementation, the annotations for `e` might have to be adapted!
  mapM_ (\(e,name,v) -> putStr (prettyName name)
          >> pprint (collectVals (e :: NDShare Bool) == v)) exBs
  mapM_ (\(e,name,v) -> putStr (prettyName name)
          >> pprint (collectVals (e :: NDShare (Pair NDShare Bool)) == v)) exPBs
  mapM_ (\(e,name,v) -> putStr (prettyName name)
          >> pprint (collectVals (e :: NDShare (List NDShare Bool)) == v)) exLBs
  mapM_ (\(e,name,v) -> putStr (prettyName name)
          >> pprint (collectVals (e :: NDShare (Pair NDShare (List NDShare Bool))) == v)) exLPBs

deriving instance Show a => Show (Pair Identity a)
deriving instance Show a => Show (List Identity a)

-- [(0,0),(0,1),(1,0),(1,1)]
dup_coin_let :: (Sharing m, MonadPlus m) => m (Int, Int)
dup_coin_let = let x = coini in duplicate x

-- [(0,0),(1,1)]
dup_coin_bind :: (Sharing m, MonadPlus m) => m (Int, Int)
dup_coin_bind = do x <- coini
                   duplicate (return x)

-- [(0,0),(1,1)]
dup_coin_share :: (Sharing m, MonadPlus m) => m (Int, Int)
dup_coin_share = do x <- share coini
                    duplicate x

-- undefined
strict_bind :: forall m. (Sharing m, MonadPlus m) => m (Int, Int)
strict_bind = do x <- undefined :: m Int
                 duplicate (const (return 2)
                                  ((return :: a -> m a) x))
-- [(2,2)]
lazy_share :: (Sharing m, MonadPlus m) => m (Int, Int)
lazy_share = do x <- share (undefined :: m Int)
                duplicate (const (return 2) x)

-- [ Cons (Identity 0) (Identity (Cons (Identity 0) (Identity Nil)))
-- , Cons (Identity 0) (Identity (Cons (Identity 1) (Identity Nil)))
-- , Cons (Identity 1) (Identity (Cons (Identity 0) (Identity Nil)))
-- , Cons (Identity 1) (Identity (Cons (Identity 1) (Identity Nil)))]
heads_bind :: (Sharing m, MonadPlus m) => m (List m Int)
heads_bind = do x <- cons coini undefined
                dupl (firstM (return x))

-- [ Cons (Identity 0) (Identity (Cons (Identity 0) (Identity Nil)))
-- , Cons (Identity 1) (Identity (Cons (Identity 1) (Identity Nil)))]
heads_share :: (Sharing m, MonadPlus m) => m (List m Int)
heads_share = do x <- share (cons coini undefined)
                 dupl (firstM x)

coinis :: MonadPlus m => m (List m Int)
coinis = nil `mplus` cons coini coinis

-- [ Cons (Identity 0) (Identity (Cons (Identity 0) (Identity Nil)))
-- , Cons (Identity 1) (Identity (Cons (Identity 1) (Identity Nil)))]
dup_first_coin :: (Sharing m, MonadPlus m) => m (List m Int)
dup_first_coin = do cs <- share coinis
                    dupl (firstM cs)
-- [ Cons (Identity 0) (Identity (Cons (Identity 0) (Identity Nil)))
-- , Cons (Identity 1) (Identity (Cons (Identity 0) (Identity Nil)))
-- , Cons (Identity 0) (Identity (Cons (Identity 1) (Identity Nil)))
-- , Cons (Identity 1) (Identity (Cons (Identity 1) (Identity Nil)))]
distrib_bind_mplus :: (Sharing m, MonadPlus m) => m (List m Int)
distrib_bind_mplus = do c <- share coini
                        y <- coini
                        x <- c
                        cons (return x) (cons (return y) nil)

exAddCoin :: NDShare Int
exAddCoin = addM coini coini

exAddSharedCoin :: NDShare Int
exAddSharedCoin = share coini >>= \fx -> addM fx fx

exAddSharedCoin2 :: NDShare Int
exAddSharedCoin2 = share coini >>= \fx -> addM (addM fx coini) (addM fx coini)

exAddSharedCoin3 :: NDShare Int
exAddSharedCoin3 = share (share coini >>= \fx -> addM fx fx) >>= \fy -> addM fy fy

exAddSharedCoin4 :: NDShare Int
exAddSharedCoin4 =
  share (share coini >>= \fx -> addM fx fx) >>=
  \fy -> share coini >>= \fz -> addM fy fz

exAddSharedCoin5 :: NDShare Int
exAddSharedCoin5 =
  share (cons coini nil) >>= \fxs -> addM (headM fxs) (headM fxs)

exAddCoinListFun :: NDShare Int -> NDShare (List NDShare Int)
exAddCoinListFun mx = do
  my <- share mx
  cons my (exAddCoinListFun (addM my coini))

exAddSharedCoin6 :: NDShare Int
exAddSharedCoin6 = do
  mx <- share (return 0)
  addM mx $ do
    my <- share (addM mx coini)
    addM my $ do
      mz <- share (addM my coini)
      addM mz (return 1)
