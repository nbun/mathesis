sort l | isSorted p = p where p = perm l

isSorted ys = case ys of
                   []     -> True
                   (x:xs) -> isSorted' x xs

isSorted' x xs = case xs of
                      [] -> True
                      (y:ys) -> x <= y && isSorted' y ys

perm ys = case ys of
               []     -> []
               (x:xs) -> insert x (perm xs)

insert  x xs = (x : xs) ? (insert2 x xs)

insert2 x xs = case xs of
                    (y:ys) -> y : insert x ys
