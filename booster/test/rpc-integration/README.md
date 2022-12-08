# How to use these tests manually

## Organisation of test files

Each set of tests resides in a directory `test-NAME`, and relates to a kore definition in `resources/NAME.kore`.
Each test in `test-NAME` consists of a "file set":

* `state-TESTNAME.json` contains the state to rewrite from, in Kore JSON format.
* `response-TESTNAME.json` contains the expected server response. The file is formatted for readability, in a way that the `rpc-client` application expects.
* (optionally) `params-TESTNAME.json` contains additional parameters (as a json object)

## How to run a test

To run a test from a test directory, do the following:

- for example, run the `zero-steps` test from `test-a-to-f`
- assuming the build output directory `.build/kore/bin` is on your path)

1) In one terminal, start the rpc server with the definition `resources/NAME.kore`:

```
$ hs-backend-booster test/rpc-integration/resources/a-to-f.kore --module TEST`
```

2) In another terminal, send `execute` requests with the respective state and parameters using the `rpc-client` tool:

```
rpc-client \
    --execute state-zero-steps.json \
    --param-file params-zero-steps.json \
    --expect response-zero-steps.json
```

3) Repeat step 2 for all tests you want to run.

4) Shut down the server in the other terminal (by pressing `^C`).

## How to add tests or update expected output

Step 2 above can be run using `--output` instead of `--expect` to (over-)write the output file and check manually that it has the expected contents.

## Automation

The shell script `runDirectoryTest.sh` runs the tests in a directory `test-NAME` given as its first argument. It will fail on the first error and automatically shut down the server.
