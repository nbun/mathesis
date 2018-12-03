#### Implementation history and key ideas for `share`

* First version, directly derived from the implementation of `catch`.

```Haskell
share :: (Share ⊂ sig) => Prog sig a -> Prog sig a
share p = do begin ; x <- p ; end ; return x
  where
    begin = inject (BShare' (return ()))
    end   = inject (EShare' (return ()))
```
This approach does not keep track of which sharing scopes were created from the
same call of `share`. For example, the expression `let x = coin in x || x` yields
the following representation.

```Haskell
BShare
  (Choice Nothing 
    (EShare (Return True))
    (EShare 
      (BShare 
        (Choice Nothing 
          (EShare (Return True)) 
          (EShare (Return False))))))
```

Since the choice is shared, both choices should receive the same ID. There is no
way to reconstruct this information from the data structure. Thus, `share` needs
provide this information.

```Haskell
share :: (Share ⊂ sig, State Int ⊂ sig) => Prog sig a -> Prog sig a
share p = do 
  i <- get
  put (i + 1)
  begin i
  x <- p
  end i
  return x
    begin i = inject (BShare' i (return ()))
    end   i = inject (EShare' i (return ()))
```

The issue with this solution is that the added state code is "executed" at the
same program level as the other instructions. This means that when the result of `share`
is duplicated due to nondeterminism, every branch will get a new ID from the state,
as shown below.

```Haskell
BShare 1
  (Choice Nothing 
    (EShare 1 (Return True))
    (EShare 1
      (BShare 2 
        (Choice Nothing 
          (EShare 2 (Return True)) 
          (EShare 2 (Return False))))))
```

To solve this problem, another program layer is added.

```Haskell
share :: (Share ⊂ sig, State Int ⊂ sig) => Prog sig a -> Prog sig (Prog sig a)
share p = do 
  i <- get
  put (i + 1)
  return $ do
    begin i
    x <- p
    end i
    return x
```

Now both program layers need to be evaluated in order to get the result. The outer
program layer defines the ID of the inner layer. When the result of the inner layer
is now duplicated, the state is already determined and the correct result, that is,
the same ID for both scopes and choices is achieved.

When only flat nondeterminism is considered, this implementation of `share` suffices.
To support data structures that can contain nondeterminism within their arguments,
some extensions are necessary.

```Haskell
share :: (Share ⊂ sig, State Int ⊂ sig) => Prog sig a -> Prog sig (Prog sig a)
share p = do 
  i <- get
  put (i + 1)
  return $ do
    begin i
    x <- p
    x' <- shareArgs share x
    end i
    return x'
```

The function `shareArgs` applies a function to all components of a data structure. In
this case, we want to share the components of a complex data structure. We consider the
example `let x = [True ? False] in (x,x)`.

```Haskell
<1 1> <2 ? 
         ├── 2> <3 3> <1 1> <4 ? 
                                 ├── 4> <5 5> ((Identity [True]),(Identity [True]))
                                 └── 4> <5 5> ((Identity [True]),(Identity [False]))
         └── 2> <3 3> <1 1> <4 ? 
                                 ├── 4> <5 5> ((Identity [False]),(Identity [True]))
                                 └── 4> <5 5> ((Identity [False]),(Identity [False]))
``` 

If we use the approach shown above, `share` does not behave as desired. Since `x` is shared,
all choices should have the same ID. 
