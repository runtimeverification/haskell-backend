# Simplifying a list concatenation expression

Similar to `../../execute/list-matching` and uses the same definition, but instead sends a simplify request.

Input:
```
{  true #Equals size(ListItem(A) ListItem (B:Int) L:List) >Int 0 }
```

Output:
```
#Top
```

See the original issue for context: https://github.com/runtimeverification/haskell-backend/issues/3749
