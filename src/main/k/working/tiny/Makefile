DEFINITION_NAME = tiny

include $(CURDIR)/../include.mk

prove_tests := \
	tiny-spec \

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)
