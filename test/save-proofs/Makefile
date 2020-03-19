DEF := save-proofs
GOLDEN += test-1-spec.k.save-proofs.kore.golden
include $(CURDIR)/../include.mk

test-1-spec.k.out: STORE_PROOFS = $(@:.out=.save-proofs.kore)

test-2-spec.k.out: RECALL_PROOFS = test-1-spec.k.save-proofs.kore
test-2-spec.k.out: test-1-spec.k.save-proofs.kore
