# Testing module addition (`"method": "add-module"`)

All tests in this directory are designed to be run in alphabetical
order, since the server state is changed by the `add-module` request.

The test uses the `a-to-f` definition but some syntax and rules from
the definition were moved into a new module that is added dynamically.

Original TEST module:
```
      a
     / \
    V   V
    b   c
        |
        V
        d
```

NEW module added on the fly:

```     d
        |
        V
        e
        |
        V
        f
```

1. Run from state c with TEST module: ends in state d
2. Attempt to run from state c with NONEXISTENT module: error
3. Add module NEW.
4. Run from state c with NEW module: ends in state f.
5. Run from state c again (use default TEST module): ends in state d
6. Run from state c with TEST module: ends in state d
