Build the `definition.kore` and copy it into the regression test directory:

```.sh
make build-haskell
cp -v .build/defn/haskell/driver-kompiled/definition.kore $KORE/test/regression-evm-semantics/
```

For each of the program tests,
copy `pgm.kore` to `⟨name⟩.kore`:

```.sh
rm -fr .krun*
env MODE=VMTESTS SCHEDULE=DEFAULT ./kevm run --backend haskell tests/ethereum-tests/VMTests/vmIOandFlowOperations/pop1.json --debug --dry-run
mv -v .krun* $KORE/test/regression-evm-semantics/pop1-pgm.kore.d
env MODE=VMTESTS SCHEDULE=DEFAULT ./kevm run --backend haskell tests/ethereum-tests/VMTests/vmArithmeticTest/add0.json --debug --dry-run
mv -v .krun* $KORE/test/regression-evm-semantics/add0-pgm.kore.d
env MODE=VMTESTS SCHEDULE=DEFAULT ./kevm run --backend haskell tests/interactive/sumTo10.evm  --debug --dry-run
mv -v .krun* $KORE/test/regression-evm-semantics/sumTo10-pgm.kore.d
```

For each of the search tests,
copy `pgm.kore` to `⟨name⟩-search.kore`
and `pattern.kore` to `⟨name⟩-search-pattern.kore`:

```.sh
rm -fr .krun*
./kevm search  --backend haskell tests/interactive/search/branching-no-invalid.evm "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>" --debug --dry-run
mv -v .krun* $KORE/test/regression-evm-semantics/branching-no-invalid-search-pgm.kore.d
./kevm search  --backend haskell tests/interactive/search/straight-line-no-invalid.evm "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>" --debug --dry-run
mv -v .krun* $KORE/test/regression-evm-semantics/straight-line-no-invalid-search-pgm.kore.d
./kevm search  --backend haskell tests/interactive/search/branching-invalid.evm "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>" --debug --dry-run
mv -v .krun* $KORE/test/regression-evm-semantics/branching-invalid-search-pgm.kore.d
./kevm search  --backend haskell tests/interactive/search/straight-line-invalid.evm "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>" --debug --dry-run
mv -v .krun* $KORE/test/regression-evm-semantics/straight-line-invalid-search-pgm.kore.d
```

For each of the proof tests,

```.sh
./kevm prove  --backend haskell tests/specs/examples/sum-to-n-spec.k --format-failures --def-module VERIFICATION --debug --dry-run
mv -v .kprove* $KORE/test/regression-evm-semantics/sum-to-n-spec.kore.d
```
