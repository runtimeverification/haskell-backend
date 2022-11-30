# JSON RPC Roundtrip tests

## Requirements

The tests in this directory are run using the python-3 script `runTests.py`.
It requires the library `jsonrpcclient` (simply use `pip install jsonrpcclient` to get it).

## Running tests

Tests are run using 

```
python3 ./runTests.py
``` 

The command will stop at the first failure, highlighting the difference to the expected output in colour.

## Updating the tests when the expected output changes

When the expected JSON output of any tests is expected to change, you can 
run the tests with `RECREATE_BROKEN_GOLDEN=true` to overwrite the golden response files

```
RECREATE_BROKEN_GOLDEN=true python3 ./runTests.py
```

While running, the script will report the differences in the output, but overwrite the old files and continue running. The idea is to inspect changes in the output, or using `git diff` after the run.

## Adding more tests to this test suite

To add a test, you will need to create a new folder in one of `execute/`, `simplify/`, etc. folders, corresponding to the API methods.
Note that the folders for the API methods may not contain anything else but subfolders with tests.

The new folder must contain input components according to the different endpoints:

* For `execute`:
  - `state.json` - a JSON Kore pattern file to be sent as the `state` parameter in the request (only necessary if we are sending `state`)
  - `params.json` - additional parameters such as `max-depth` for the execute function
* For `implies`:
  - `antecedent.json` - a JSON Kore pattern file containing the antecedent term
  - `consequent.json` - a JSON Kore pattern file containing the consequent term
* For `simplify`:
  - `state.json` - a JSON Kore pattern file containing the state to simplify

For all endpoints:
* `definition.kore` - the definition file with a module `TEST` (this module name is hard coded for all tests)
* `response.golden` - golden file with the expected response from the server

Optionally, other files can be included, for instance

* `test.k` - the K definition compiled to `definition.kore`
* `state.test` - the start state for `execute` in the format of the source code


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
CREATE_MISSING_GOLDEN=true python3 ./runTests.py
```

Clean up the folder and commit the new test

