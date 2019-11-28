DEFINITION_NAME := unification

include $(CURDIR)/../../include.mk

prove_tests := \
	function-unification-spec \

test: test-k

test-k: test-prove

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)

golden: $(foreach test, $(prove_tests), prove/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test test-prove golden clean %.test %.krun
