-- Pretty printing of choice trees
module Pretty where
import           Data.Functor.Identity
import           Tree

class Pretty a where
  pretty  :: a -> String
  -- Pretty function with whitespace indentation level
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

-- Is a string surrounded by parentheses?
isPared :: String -> Bool
isPared (c:cs) | c == '(' && last cs == ')' = True
isPared _      = False

par :: String -> String
par s = "(" ++ s ++ ")"

-- Adds parentheses only if necessary
prettyPar :: (Pretty a) => String -> a -> String
prettyPar s x = let r = pretty x
                in s ++ " " ++ if isPared r then r else par r

showID :: Show a => Maybe a -> String
showID = maybe "" show

-- Prints lines of choice branches
printLines :: [Int] -> String
printLines = printLines' 0 . reverse
  where
    printLines' p  [x] = replicate (x - p) ' '
    printLines' p (x:xs)  | p == x    = '│' : printLines' (p + 1) xs
                          | otherwise = ' ' : printLines' (p + 1) (x:xs)
