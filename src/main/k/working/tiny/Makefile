DEFINITION_NAME = tiny

include $(CURDIR)/../include.mk

prove_tests := \
	trusted-claim-spec \

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)
