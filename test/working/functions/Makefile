DEFINITION_NAME := functions

include $(CURDIR)/../include.mk

prove_tests := \
	positive-spec \
	positive-requires-spec \
	length-spec \
	length-cons-spec \

test: test_prove

test-k: test-prove

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)

golden:

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
