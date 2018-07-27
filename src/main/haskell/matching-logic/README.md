# Matching Logic implementation

To build: `stack build`.
All dependencies are managed by stack.

To run the tests: `stack test --coverage` or `stack test --no-keep-going` or
`stack test --test-arguments --hide-successes`.

To regenerate the golden data for regression tests:
`stack test --no-keep-going --ta --accept`

To generate documentation: `stack build --haddock`.

## Debugging

If building the test suite fails with some undecipherable error, add

> -optF --debug

to the `OPTION_GHC` pragma in `test/Driver.hs`. The option will cause
`tasty-debug` to print the generated source code to the terminal; hopefully,
this reveals the error.
