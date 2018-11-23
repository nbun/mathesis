module Pretty where
import Tree
import Data.Functor.Identity

class Pretty a where
  pretty :: a -> String
  pretty' :: a -> Int -> String
  pretty' x _ = pretty x

instance Pretty a => Pretty (Identity a) where
  pretty (Identity x) = "(Identity " ++ pretty x ++ ")"

instance Pretty Bool where
  pretty = show

instance Pretty Int where
  pretty = show

instance Pretty a => Pretty (Tree a) where
  pretty t = pretty' t 0

  pretty' Failed   _ = "_|_"
  pretty' (Leaf x) _ = pretty x
  pretty' (Choice n t1 t2) wsp =
    show n ++ "\n" ++ replicate wsp ' ' ++ "|---- " ++ pretty' t1 (wsp+6)
           ++ "\n" ++ replicate wsp ' ' ++ "|---- " ++ pretty' t2 (wsp+6)

pprint :: Pretty a => a -> IO ()
pprint = putStrLn . pretty
