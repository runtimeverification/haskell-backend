DEFINITION_NAME := path
MODULE_NAME := PATH

include $(CURDIR)/../../../include.mk

all_tests := $(k_tests)

k_tests := $(not_prove_tests) $(prove_tests)

not_prove_tests := \
	distinct-spec
prove_tests := \
	identity-spec

test: $(foreach test, $(all_tests), notprovable/$(test).test)

test-k: $(foreach test, $(k_tests), tests/$(test).test) \
	test-unprove

#test-prove: $(foreach test, $(prove_tests), provable/$(test).kprove)

test-unprove: $(foreach test, $(not_prove_tests), notprovable/$(test).knotprove.test)

golden: $(foreach test, $(not_prove_tests), notprovable/$(test).knotprove.output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
