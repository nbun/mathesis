-- Pretty printing of choice trees
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

instance (Pretty a, Pretty b) => Pretty (a,b) where
  pretty (x,y) = "(" ++ pretty x ++ "," ++ pretty y ++ ")"

pprint :: Pretty a => a -> IO ()
pprint = putStrLn . pretty

isPared :: String -> Bool
isPared (c:cs) | c == '(' && last cs == ')' = True
isPared _ = False

par :: String -> String
par s = "(" ++ s ++ ")"

prettyPar :: (Pretty a) => String -> a -> String
prettyPar s x = let r = pretty x
                in s ++ " " ++ if isPared r then r else par r
