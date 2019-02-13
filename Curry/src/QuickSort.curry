module QuickSort where
import List

quicksort :: Ord a => (a -> a -> Bool) -> [a] -> [a]
quicksort _ []     = []
quicksort p (x:xs) = let part = partition (p x) xs
                     in quicksort p (fst part) ++ [x] ++ quicksort p (snd part)
