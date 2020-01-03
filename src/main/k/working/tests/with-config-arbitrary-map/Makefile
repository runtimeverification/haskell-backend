DEFINITION_NAME := with-config

include $(CURDIR)/../../include.mk

test-prove: prove/one-spec.kprove

test-k: test-prove

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun test-prove
