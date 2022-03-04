These are the tests for integration between the K frontend and the Haskell backend.

`Makefile` targets:

- `test`: Run the tests.
- `golden`: Update the expected outputs.
- `clean`

Each directory contains a number of tests based on a single K definition.
The tests require the K frontend to be installed;
by default a suitable version will be installed at `../.build/k`.


## Program tests

Program tests run a concrete program with `krun`
and compare the output to an expected ("golden") file.
Program tests have filenames of the form `⟨name⟩.⟨ext⟩`
where `⟨name⟩` is the (arbitrary) name of the test
and `⟨ext⟩` is the filename extension used by the definition.
By default, if the definition filename is `⟨def⟩.k` then `⟨ext⟩ = ⟨def⟩`,
otherwise the `Makefile` will contain the line `EXT = ⟨ext⟩`.
A test fails when the actual and expected output differ.
The exit code of `krun` is not considered,
so one may write program tests which encounter errors.

`Makefile` targets:

- `make ⟨name⟩.⟨ext⟩.out`:
  Run the named test and compare the output to `⟨name⟩.⟨ext⟩.out.golden`.
  The test passes if the expected and actual output are identical.
  The test will not run again until the test prerequisites change
  or `⟨name⟩.⟨ext⟩.out` is deleted.
  If the test fails, the actual output is moved
  from `⟨name⟩.⟨ext⟩.out` to `⟨name⟩.⟨ext⟩.out.fail`.
- `make ⟨name⟩.⟨ext⟩.out.golden`:
  Run the test to construct `⟨name⟩.⟨ext⟩.out.golden`.


## Specification tests

Specification tests prove a number of claims with `kprove`
and compare the output to an expected ("golden") file.
Specification tests have filenames of the form `⟨name⟩-spec.k`.
The specification must have the following form:

```.k
module VERIFICATION
  imports ⟨DEF⟩  // ⟨DEF⟩ is the definition module defined in ⟨def⟩.k
endmodule

module ⟨NAME⟩-SPEC  // ⟨NAME⟩ must be the upper-case of ⟨name⟩
  imports VERIFICATION

  // CLAIMS

endmodule
```

A test fails when the actual and expected output differ.
The exit code of `kprove` is not considered,
so one may write program tests which encounter errors.

`Makefile` targets:

- `make ⟨name⟩-spec.k.out`:
  Run the named test and compare the output to `⟨name⟩-spec.k.out.golden`.
  The test passes if the expected and actual output are identical.
  The test will not run again until the test prerequisites change
  or `⟨name⟩-spec.k.out` is deleted.
  If the test fails, the actual output is moved
  from `⟨name⟩-spec.k.out` to `⟨name⟩-spec.k.out.fail`.
- `make ⟨name⟩-spec.k.out.golden`:
  Run the test to construct `⟨name⟩-spec.k.out.golden`.

### KBMC

To run a specification test with `kbmc` instead of `kprove`,
it should be named like `⟨name⟩-bmc-spec.k`.
In the `Makefile`, the depth should be set by a target-specific variable:

```
⟨name⟩-bmc-spec.k: KBMC_DEPTH = 20
```

### REPL

To run a specification test with `kore-repl` instead of `kore-exec`,
it should be named like `⟨name⟩-repl-spec.k`.
To run a specification test with `kore-repl` using a specific script,
it should be named like `⟨name⟩-repl-script-spec.k`
and the script should be in a file named `⟨name⟩-repl-script-spec.k.repl`.

## Saving proofs

To save intermediate proofs from a specification test,
set the target-specific variable `STORE_PROOFS`:

```
test-1-spec.k.out: STORE_PROOFS = $(@:.out=.save-proofs.kore)
```

The test will now compare `test-1-spec.k.out` to `test-1-spec.k.out.golden`
and compare `test-1-spec.k.save-proofs.kore` to `test-1-spec.k.save-proofs.kore.golden`.

To re-use intermediates from a previous test,
set the target-specific variable `RECALL_PROOFS`:

```
test-2-spec.k.out: RECALL_PROOFS = test-1-spec.k.save-proofs.kore
test-2-spec.k.out: test-1-spec.k.save-proofs.kore
```

You must add a dependency on the saved proofs
as in the second line above!


## Scripted tests

Any script named `test-⟨name⟩.sh` will be treated as a test.

`Makefile` targets:

- `make test-⟨name⟩.sh.out`:
  Run the named test and compare the output to `test-⟨name⟩.sh.out.golden`.
  The test passes if the expected and actual output are identical.
  The prerequisites are any files matching the pattern `test-⟨name⟩-*`.
  The test will not run again until the test prerequisites change
  or `test-⟨name⟩.sh.out` is deleted.
  If the test fails, the actual output is moved
  from `test-⟨name⟩.sh.out` to `test-⟨name⟩.sh.out.fail`.
- `make test-⟨name⟩.sh.out.golden`:
  Run the test to construct `test-⟨name⟩.sh.out.golden`.


## Definitions

To add a new definition, create a new directory containing one-line `Makefile`:

```
include $(CURDIR)/../include.mk
```

In the new directory, create a K definition named `test.k`.
Add program or specification tests as described above.

`Makefile` targets:

- `make test-kompiled/definition.kore`:
  `kompile` the definition.
