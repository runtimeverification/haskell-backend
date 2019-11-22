DEFINITION_NAME := path
MODULE_NAME := PATH

include $(CURDIR)/../../../include.mk

not_prove_tests :=
prove_tests := \
	all-path-f-spec

test: test-k

test-k: test-unprove test-prove

test-prove: $(foreach test, $(prove_tests), provable/$(test).kprove)

test-unprove: $(foreach test, $(not_prove_tests), notprovable/$(test).knotprove.test)

golden: $(foreach test, $(not_prove_tests), notprovable/$(test).knotprove.output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
