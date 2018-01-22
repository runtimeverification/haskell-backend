# Kore parser

First time: `stack init`.

To build: `stack build`.
All dependencies are managed by stack.

To run: `stack exec kore-parser FILE`.

To run the tests: `stack test --coverage` or `stack test --no-keep-going` or
`stack test --test-arguments --hide-successes`.

To regenerate the golden data for regression tests:
`stack test --no-keep-going --ta --accept`

To generate documentation: `stack build --haddock`.