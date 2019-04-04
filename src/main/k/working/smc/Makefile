DEFINITION_NAME = smc

include $(CURDIR)/../include.mk

all_tests := \
	collatz \
	primes \
	sum
k_tests := \
	sum
prove_tests := \
	add-spec \
	max-spec \
	sum-spec \
	double-sum-spec \
	add-stack-spec \
	max-stack-spec \
	sum-stack-spec \

test: $(foreach test, $(all_tests), tests/$(test).test)

test-k: $(foreach test, $(k_tests), tests/$(test).test) \
	test-prove

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)

golden: $(foreach test, $(all_tests), tests/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
