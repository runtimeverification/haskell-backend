# JSON RPC ROundtrip tests

This README provides a guide for adding more tests to this test suite.

To add a test, you wil need to create a new folder in one of `execute/`, `simplify/`, etc. folders, corresponding to the API methods.

The new folder must contain:

* `definition.kore` - the definition file with a module `TEST` (this module name is hard coded for all tests)
* `state.json` - a JSON Kore pattern file to be sent as the `state` parameter in the request (only necessary if we are sending `state`)
* `params.json` - should contain additional parameters such as `max-depth` for the execute function
* `response.golden` - golden file with the expected response from the server

Optionally also include:

* `test.k`
* `state.test`


## How to generate the above files

Starting from `definition.k` and `state.k` we fist compile `definition.k` into core

```shell
# (optional) bring k into scope via nix
nix shell github:runtimeverification/k
# kompile agains the haskell backend
kompile  --backend haskell definition.k
# copy the resulting definition.kore
cp test-kompiled/definition.kore .
```

Next we convert `state.test` into `state.kore`

```
kast -o KORE state.test > state.kore
```

Finally we use `kore-parser` to generate a JSON representation of textual kore for state

```
kore-parser definition.kore --module TEST --pattern state.kore --print-pattern-json > state.json
```

Finally, run the tests with `CREATE_MISSING_GOLDEN=true` to generate a golden response

```
CREATE_MISSING_GOLDEN=true ./runTests.py
```

Clean up the folder and commit the new test