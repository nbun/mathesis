module PFLNDP where
import           Control.Monad

------------------------------------------
-- Naive MonadPlus approach
------------------------------------------

insert :: MonadPlus m => a -> [a] -> m [a]
insert x xs = return (x:xs)
      `mplus` case xs of
                []     -> mzero
                (y:ys) -> do zs <- insert x ys
                             return (y:zs)

perm :: MonadPlus m => [a] -> m [a]
perm [] = return []
perm (x:xs) = do ys <- perm xs
                 zs <- insert x ys
                 return zs

sort :: MonadPlus m => [Int] -> m [Int]
sort xs = do ys <- perm xs
             guard (isSorted ys)
             return ys

isSorted :: Ord a => [a] -> Bool
isSorted (x:y:xs) | x <= y = isSorted (y:xs)
                  | otherwise = False
isSorted _ = True

hd :: MonadPlus m => [Int] -> m Int
hd []     = mzero
hd (x:xs) = return x

------------------------------------------
-- Monadic components approach
------------------------------------------

data List m a = Nil | Cons (m a) (m (List m a))

nil :: Monad m => m (List m a)
nil = return Nil

cons :: Monad m => m a -> m (List m a) -> m (List m a)
cons x y = return (Cons x y)

fromList :: Monad m => m (List m a) -> m [a]
fromList m = do
  xs <- m
  case xs of
    Nil -> return []
    Cons y ys -> do
      z <- y
      zs <- fromList ys
      return (z:zs)

toList :: Monad m => [a] -> m (List m a)
toList []     = nil
toList (x:xs) = cons (return x) (toList xs)

isSorted' :: (Ord a, MonadPlus m) => m (List m a) -> m Bool
isSorted' ml = ml >>= \l ->
  case l of
    Cons mx mxs -> mxs >>= \xs ->
      case xs of
        Cons my mys -> mx >>= \x -> my >>= \y ->
         if x <= y then isSorted' (cons (return y) mys)
         else return False
        _ -> return True
    _ -> return True

insert' :: MonadPlus m => m a -> m (List m a) -> m (List m a)
insert' mx mxs = cons mx mxs
  `mplus` do xs <- mxs
             case xs of
               Nil         -> mzero
               Cons my mys -> cons my (insert' mx mys)

perm' :: MonadPlus m => m (List m a) -> m (List m a)
perm' ml = ml >>= \l ->
  case l of
    Nil         -> nil
    Cons mx mxs -> insert' mx (perm' mxs)

sort' :: MonadPlus m => m (List m Int) -> m (List m Int)
sort' xs = let ys = perm' xs in
  isSorted' ys >>= \sorted -> guard sorted >> ys

hd' :: MonadPlus m => m (List m a) -> m a
hd' mxs = mxs >>= \xs -> case xs of
                           Nil      -> mzero
                           Cons x _ -> x
