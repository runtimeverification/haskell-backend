## Smoke tests for definition serialisation

A few large kore files (from other regression tests) are serialised using the `--serialize` option:

```shell
$ kore-exec --serialize FILENAME.kore --output serialized.bin --module MODULE
```
The `MODULE` variable needs to be set for each test (see `Makefile`)

Then the serialised definition is loaded back into memory by a call to `kore-exec` which fails on a sanity check after loading the definition:

```shell
$ kore-exec serialized.bin --module MODULE --pattern DUMMY --debug-rewrite FAIL-ME-PLEASE
```
The expected failure is

```
kore-exec: [NUMBER] Error (ErrorException):
    Rule labels for the following debug options are not defined:
    --debug-rewrite: FAIL-ME-PLEASE
```
Presence of the error is checked by piping output to `grep FAIL-ME-PLEASE`.

This is the best we can do because of some assumptions hard-coded into `kore-exec`[1], and because we must use the exact same executable to write and read the serialised file.

[1] For instance, the binary file must have suffix `.bin` and an adjacent `definition.kore` file must exist when using a binary file.
