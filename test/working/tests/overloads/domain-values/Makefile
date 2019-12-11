DEFINITION_NAME := domain-values

include $(CURDIR)/../../../include.mk

test-prove: prove/domain-values-spec.kprove

test-k: test-prove

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun test-prove
