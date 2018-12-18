#### Implementation history and key ideas for `share`

* First version, directly derived from the implementation of `catch`.

```Haskell
share :: (Share <: sig) => Prog sig a -> Prog sig (Prog sig a)
share p = do begin ; x <- p ; end ; return x
  where
    begin = inject (BShare' (return ()))
    end   = inject (EShare' (return ()))
```
This approach does not keep track of which sharing scopes were created from the
same call of `share`. For example, the expression `let x = coin in x || x` yields
the following representation where `<` and `>` mark the beginning and end of a
scope, respectively. Choices are represented by `?`.

```Haskell
< ? 
  ├── > True
  └── > < ? 
           ├── > True
           └── > False
```

Since the choice is shared, both choices should receive the same ID. There is no
way to reconstruct this information from the data structure. Thus, `share` needs
provide this information.

```Haskell
share :: (Share <: sig, State Int <: sig) => Prog sig a -> Prog sig a
share p = do 
  i <- get
  put (i + 1)
  begin i
  x <- p
  end i
  return x
    begin i = inject (bshare' i (return ()))
    end   i = inject (eshare' i (return ()))
```

The issue with this solution is that the added state code is "executed" at the
same program level as the other instructions. This means that when the result of `share`
is duplicated due to nondeterminism, every branch will get a new ID from the state,
as shown below.

```Haskell
<1 ? 
   ├── 1> True
   └── 1> <2 ? 
             ├── 2> True
             └── 2> False
```

To solve this problem, another program layer is added.

```Haskell
share :: (Share <: sig, State Int <: sig) => Prog sig a -> Prog sig (Prog sig a)
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
share :: (Share <: sig, State Int <: sig) => Prog sig a -> Prog sig (Prog sig a)
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
         │                     ├── 4> <5 5> ((Identity [True]),(Identity [True])) 
         │                     └── 4> <5 5> ((Identity [True]),(Identity [False]))
         └── 2> <3 3> <1 1> <4 ? 
                               ├── 4> <5 5> ((Identity [False]),(Identity [True]))
                               └── 4> <5 5> ((Identity [False]),(Identity [False]))
``` 

If we use the approach shown above, `share` does not behave as desired. Since `x` is shared,
all choices should have the same ID. Although flat share scopes receive the correct IDs due
to the outer program layer, nested calls of share do not work correctly because they depend
on the state of the inner program, which depends on when and in which order the inner programs
are evaluated. Thus, we need to give each inner program a unique state from which the remaining
computation can be continued.

```Haskell
share :: (Share <: sig, State Int <: sig) => Prog sig a -> Prog sig (Prog sig a)
share p = do 
  i <- get
  put (i + 1)
  return $ do
    begin i
    -- put ?
    x <- p
    x' <- shareArgs share x
    end i
    return x'
```

Nested calls of `share` can also occur in `p`. Thus, the new state needs to be set before binding
`p`. One question remains: What should be the new state? If we put the same state `i + 1` in the
inner program, we can observe ID collisions as in the following example.

```Haskell
let xs = let ys = [coin] 
         in ys ++ ys 
in let x = coin
       y = coin
   in x : y : xs
```

If example results in the tree below.

```
? (2,1)
├── ? (3,1)
│   ├── ? (3,1)
│   │   ├── ? (3,1)
│   │   │   ├── [True,True,True,True]
│   │   │   └── [True,True,True,False]
```

The correct tree should have different choice IDs on choice depth level 3 and 4.

```
? (2,1)
├── ? (4,1)
│   ├── ? (7,1)
│   │   ├── ? (7,1)
│   │   │   ├── [True,True,True,True]
│   │   │   └── [True,True,True,False]
```

One easy fix to achieve this result is to make the new IDs unique by splitting the ID supply
into two new, independent supplies, for example, as shown in the following.

```Haskell
share :: (Share <: sig, State Int <: sig) => Prog sig a -> Prog sig (Prog sig a)
share p = do 
  i <- get
  put (i * 2)
  return $ do
    begin i
    put (i * 2 + 1)
    x <- p
    x' <- shareArgs share x
    end i
    return x'
```

Another unmentioned detail is the second component of the choice ID. This is approach is necessary
when multiple choices occur within in the same `share` scope, for example as in `let x = coin ? coin in x || x`.

```Haskell
? (1,1)
├── ? (1,2)
│   ├── True
│   └── ? (1,1)
│       ├── ? (1,2)
│       │   ├── True
│       │   └── False
│       └── ? (1,3)
│           ├── True
│           └── False
└── ? (1,3)
    ├── True
    └── ? (1,1)
        ├── ? (1,2)
        │   ├── True
        │   └── False
        └── ? (1,3)
            ├── True
            └── False
```

Here we only one `share` ID (the first component) but three different IDs for the nested choices within
the `share` scope.
