#!/usr/bin/env bash

grab_krun() {
  mv -v .krun*/pgm.kore $KORE/test/regression-evm-semantics/$1-pgm.kore
  rmdir .krun*
}

grab_krun_search() {
  mv -v .krun*/pgm.kore $KORE/test/regression-evm-semantics/$1-search-pgm.kore
  mv -v .krun*/pattern.kore $KORE/test/regression-evm-semantics/$1-pattern.kore
  rmdir .krun*
}

grab_kprove() {
  mv -v .kprove*/spec.kore $KORE/test/regression-evm-semantics/$1-spec.kore
  mv -v .kprove*/vdefinition.kore $KORE/test/regression-evm-semantics/$1-vdefinition.kore
  rmdir .kprove*
}

make build-haskell
cp -v .build/defn/haskell/driver-kompiled/definition.kore $KORE/test/regression-evm-semantics/

rm -fr .krun* .kprove*

env MODE=VMTESTS SCHEDULE=DEFAULT ./kevm run --backend haskell tests/ethereum-tests/VMTests/vmIOandFlowOperations/pop1.json --debug --dry-run
grab_krun pop1

env MODE=VMTESTS SCHEDULE=DEFAULT ./kevm run --backend haskell tests/ethereum-tests/VMTests/vmArithmeticTest/add0.json --debug --dry-run
grab_krun add0

env MODE=VMTESTS SCHEDULE=DEFAULT ./kevm run --backend haskell tests/interactive/sumTo10.evm  --debug --dry-run
grab_krun sumTo10

./kevm search  --backend haskell tests/interactive/search/branching-no-invalid.evm "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>" --debug --dry-run
grab_krun_search branching-no-invalid

./kevm search  --backend haskell tests/interactive/search/straight-line-no-invalid.evm "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>" --debug --dry-run
grab_krun_search straight-line-no-invalid

./kevm search  --backend haskell tests/interactive/search/branching-invalid.evm "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>" --debug --dry-run
grab_krun_search branching-invalid

./kevm search  --backend haskell tests/interactive/search/straight-line.evm "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>" --debug --dry-run
grab_krun_search straight-line

./kevm prove  --backend haskell tests/specs/examples/sum-to-n-spec.k --format-failures --def-module VERIFICATION --debug --dry-run
grab_kprove sum-to-n
