DEFINITION_NAME := imp
MODULE_NAME := IMP

include $(CURDIR)/../include.mk

all_tests := \
	collatz \
	impossible-branch.psearch.final \
	impossible-branch.search.final \
	max-symbolic.search.final \
	primes \
	sum
k_tests := \
	impossible-branch.psearch.final \
	sum
prove_tests := \
	add-spec \
	max-spec \
	sum-spec \
	sum-div-spec \
	double-sum-spec \

broken_prove_tests := \
	disjunction-in-simplification-spec

merge_tests := \
    1 \
    2

save_claims_tests := \
	sum-spec

test: $(foreach test, $(all_tests), tests/$(test).test)

test-k: $(foreach test, $(k_tests), tests/$(test).test) \
	test-prove \
	test-broken-prove \
	test-merge \
	test-save-proofs

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)

test-broken-prove: $(foreach test, $(broken_prove_tests), prove/$(test).kbroken-prove)

golden: $(foreach test, $(all_tests), tests/$(test).output.golden)

test-merge: $(foreach test, $(merge_tests), merge/$(test).merge-test)

merge-golden: $(foreach test, $(merge_tests), merge/$(test).merge-golden)

test-save-proofs: \
	$(foreach test, $(save_claims_tests), save-proofs/$(test).save-proofs-test)

save-proofs-golden: \
	$(foreach test, \
		$(save_claims_tests), \
		save-proofs/$(test).save-proofs-golden \
	)

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden merge-golden clean %.test %.krun
