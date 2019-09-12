DEFINITION_NAME := test

include $(CURDIR)/../../../include.mk

test: test-spec.kprove

test-k: test

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
