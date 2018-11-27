{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}

module TestSharing where

import           Control.Monad         (MonadPlus (..))
import           Data.Functor.Identity (Identity (..))
import           Pretty                (pprint)
import Base
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
                                    Cons fy fys -> share fys >>= \fys' -> cons fy (fys' `mplus` recList fys')

exRecList :: (Sharing m, MonadPlus m) => m (Pair m (List m Bool))
exRecList = share (recList (cons (return True) (cons (return False) nil))) >>= \fx -> pairM fx fx

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

-- let x = True ? False in x ? x
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


-- exShareSingleton :: NDShare (Pair NDShare (List NDShare Bool))
-- exShareSingleton = do
--   fx <- do
--     i <- get
--     put (i + 1)
--     return $ do
--       inject (BShare' i (return ()))
--       x <- (cons (return True `mplus` return False) nil)
--       x' <- shareArgs share x
--       inject (EShare' i (return ()))
--       return x'
--   pairM fx fx

-- exShareSingleton :: NDShare (Pair NDShare (List NDShare Bool))
-- exShareSingleton = do
--   fx <- do
--     i <- get
--     put (i + 1)
--     return $ do
--       inject (BShare' i (return ()))
--       x' <- shareArgs share (Cons (return True `mplus` return False) nil)
--       inject (EShare' i (return ()))
--       return x'
--   pairM fx fx

-- exShareSingleton :: NDShare (Pair NDShare (List NDShare Bool))
-- exShareSingleton = do
--   fx <- do
--     i <- get
--     put (i + 1)
--     return $ do
--       inject (BShare' i (return ()))
--       x' <- do sy' <- share (return True `mplus` return False)
--                sys' <- share nil
--                cons sy' sys'
--       inject (EShare' i (return ()))
--       return x'
--   pairM fx fx

-- exShareSingleton :: NDShare (Pair NDShare (List NDShare Bool))
-- exShareSingleton = do
--   fx <- do
--     i <- get
--     put (i + 1)
--     return $ do
--       inject (BShare' i (return ()))
--       x' <- do sy' <- do
--                  i <- get
--                  put (i + 1)
--                  return $ do
--                    inject (BShare' i (return ()))
--                    x <- (return True `mplus` return False)
--                    x' <- shareArgs share x
--                    inject (EShare' i (return ()))
--                    return x'
--                sys' <- share nil
--                cons sy' sys'
--       inject (EShare' i (return ()))
--       return x'
--   pairM fx fx

-- exShareSingleton :: NDShare (Pair NDShare (List NDShare Bool))
-- exShareSingleton = do
--   fx <- do
--     i <- get
--     put (i + 1)
--     return $ do
--       inject (BShare' i (return ()))
--       x' <- do sy' <- do
--                  i <- get
--                  put (i + 1)
--                  return $ do
--                    inject (BShare' i (return ()))
--                    x' <- shareArgs share True `mplus` shareArgs share False
--                    inject (EShare' i (return ()))
--                    return x'
--                sys' <- share nil
--                cons sy' sys'
--       inject (EShare' i (return ()))
--       return x'
--   pairM fx fx

-- exShareSingleton :: NDShare (Pair NDShare (List NDShare Bool))
-- exShareSingleton = do
--   fx <- do
--     i <- get
--     trace (show i) $ put ((i :: Int) + 1)
--     return $ do
--       inject (BShare' i (return ()))
--       x' <- do sy' <- do
--                  j <- get
--                  put (j + 1)
--                  return $ do
--                    inject (BShare' j (return ()))
--                    x' <- return True `mplus` return False
--                    inject (EShare' j (return ()))
--                    return x'
--                sys' <- do
--                  k <- get
--                  put (k + 1)
--                  return $ do
--                    inject (BShare' k (return ()))
--                    x' <- nil
--                    inject (EShare' k (return ()))
--                    return x'
--                cons sy' sys'
--       inject (EShare' i (return ()))
--       return x'
--   pairM fx fx

-- exShareSingleton :: (Sharing m, MonadPlus m) => m (Pair m (List m Bool))
-- exShareSingleton = do
--   fx <- share $ return True `mplus` return False
--   fy <- share nil
--   fxs <- share (cons fx fy)
--   pairM fxs fxs

-- exShareSingleton :: (Sharing m, MonadPlus m) => m (Pair m (List m Bool))
-- exShareSingleton = (cons (return True `mplus` return False) nil) >>= \xs ->
--   (share $ case xs of
--     Cons fy fys -> share fy >>= \fy' -> share fys >>= \fys' -> cons fy' fys'
--     Nil         -> nil) >>= \fxs -> pairM fxs fxs

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

deriving instance Show a => Show (Pair Identity a)
deriving instance Show a => Show (List Identity a)
