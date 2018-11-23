{-# LANGUAGE TypeOperators #-}
module Tree where

data Tree a = F
            | L a
            | C (Maybe Int) (Tree a) (Tree a)
  deriving Show

class Pretty a where
  pretty :: a -> String
  pretty' :: a -> Int -> String

instance Pretty Bool where
  pretty = show
  pretty' x _ = pretty x


instance Pretty Int where
  pretty = show
  pretty' x _ = pretty x

instance (Show a, Show b) => Pretty (a,b) where
  pretty = show
  pretty' x _ = pretty x

instance Pretty a => Pretty (Tree a) where
  pretty t = pretty' t 0

  pretty' F _ = "_|_"
  pretty' (L x) _ = pretty x
  pretty' (C n t1 t2) wsp =
    show n ++ "\n" ++ replicate wsp ' ' ++ "|---- " ++ pretty' t1 (wsp+6)
           ++ "\n" ++ replicate wsp ' ' ++ "|---- " ++ pretty' t2 (wsp+6)
