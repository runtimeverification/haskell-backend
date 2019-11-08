DEFINITION_NAME := locals

include $(CURDIR)/../include.mk

proofs := \
	locals-spec \

test: test-prove

test-k: test-prove

test-prove: $(foreach proof, $(proofs), proofs/$(proof).kprove)

golden:

clean:
	rm -rf $(KOMPILED) proofs/*.output

.PHONY: test-k test golden clean %.test %.krun
