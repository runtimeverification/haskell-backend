## Integration tests for JSON classification and comparison tool

This directory contains input files for tests in
`Test.Booster.JsonRpc.DiffTest`.

### File Classification

Files in this directory are named according to their expected
classification by `decodeKoreJson`, with suffixes indicating the
expected `KoreRpcType`:

| Suffix               | `KoreRpcType`        |                                     |
|----------------------|----------------------|-------------------------------------|
| `.<method>.request`  | `RpcReq <Method-M>`  | Request with given method           |
| `.<method>.response` | `RpcResp <Method-M>` | Response for given method           |
| `.error.response`    | `RpcErr`             | Error response {msg, code, details} |
| `.kore.json`         | `RpcKore`            | JSON-encoded Kore term              |
| `.random.json`       | `RpcJs`              | Valid JSON of unknown type          |
| `.error`             | `NotRpcJs`           | Not valid as JSON                   |

The test reads and classifies the file, comparing against the expected
type given by the suffix.

### File comparisons

The files in this directory are compared _pairwise_ with each
other. The comparison results are rendered as file differences or type
differences.

The output of the comparison is compared to expected outputs stored in
files in subdirectory `expected/`.
The expected output of comparing `<file1>` and `<file2>` is stored in
`<basename file1>@<basename file2`
