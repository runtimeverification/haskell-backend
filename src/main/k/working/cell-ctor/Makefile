DEFINITION_NAME := cell-ctor

include $(CURDIR)/../include.mk

prove_tests := \
	cell-ctor-spec \

test: test-prove

test-k: test-prove

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)

golden:

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
