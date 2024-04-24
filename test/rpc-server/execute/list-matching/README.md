# Simplifying a list concatenation expression

The rewrite rule in `test.k` introduces a symbolic list expression into the path condition, that is immediately simplified to `true` by the `simplify-size` simplification.

See the original issue for context: https://github.com/runtimeverification/haskell-backend/issues/3749
