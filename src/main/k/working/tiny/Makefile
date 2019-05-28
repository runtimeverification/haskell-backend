DEFINITION_NAME = tiny

include $(CURDIR)/../include.mk

prove_tests := \
	tiny-spec \

kscript_tests := \
	trusted-claims \

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)

# test-kscript: $(foreach test, $(kscript_tests), repl-tests/$(test).kscript)
