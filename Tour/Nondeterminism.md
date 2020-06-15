# Non-determinism

In **Edh** the `for-from-do` loop, combined with `generator` procedures,
are much like a procedural version of **Haskell**'s list Monad,
modeling non-determinism as well.

Take the example in
[this blog post](https://deque.blog/2017/09/04/list-monad-and-np-complexity/)

```hs
satExample :: Bool
satExample = or $ do
  x1 <- [True, False] -- "guess" is replaced by bind (<-)
  x2 <- [True, False]
  {- ... -}
  xN <- [True, False]
  pure (formula x1 x2 {- ... -} xN)
```

This is exactly the same thing in **Edh**

```edh
method satExample() or ({generator _ ()
  for x1 from [true, false] do
  for x2 from [true, false] do
  # ...
  for xN from [true, false] do
  yield formula (
    x1, x2,
    # ...,
    xn
  )
})
```

The utility procedure `or`'s **Edh** implementation:

```edh
method or ( possibles ) {
  for predict from possibles() do
    predict -> return true
  return false
}
```
