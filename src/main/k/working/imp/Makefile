DEFINITION_NAME := imp

include $(CURDIR)/../include.mk

all_tests := \
	collatz \
	impossible-branch.search.final \
	max-symbolic.search.final \
	primes \
	sum
k_tests := \
	impossible-branch.search.final \
	sum
prove_tests := \
	add-spec \
	max-spec \
	sum-spec \
	sum-div-spec \
	double-sum-spec \

test: $(foreach test, $(all_tests), tests/$(test).test)

test-k: $(foreach test, $(k_tests), tests/$(test).test) \
	test-prove

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)

golden: $(foreach test, $(all_tests), tests/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
