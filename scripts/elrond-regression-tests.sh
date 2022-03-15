set -eu

prep-elrond() {
    cd $KORE
    git clone git@github.com:runtimeverification/elrond-multisig.git
    cd elrond-multisig
    cd kompile-tool
    ./prepare-k.sh
    cd ..
    bazel clean
}

run-elrond() {
    cd $KORE/elrond-multisig
    bazel run //protocol-correctness/proof/lemmas/0/signers:lemma-at-most-this-signer-0-count-can-sign-function
    bazel run //protocol-correctness/proof/lemmas/1/list/contains:lemma-list-contains-last-to-start
    bazel run //protocol-correctness/proof/functions:proof-change-user-role-New
    bazel run //protocol-correctness/proof/functions:proof-perform-action-add-proposer-None
    bazel run //protocol-correctness/proof/malicious-user/can-be-deleted/run-external-call-from-user:proof-recfu-sign-error
}

export KORE=$(pwd)
prep-elrond
run-elrond
rm -rf elrond-multisig
