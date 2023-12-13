To regenerate the json files in this directory:

```
stack repl --test kore:test:kore-test
ghci> :load Test.Kore.Syntax.Json.Roundtrips
ghci> makeGold
```
