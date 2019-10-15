DEFINITION_NAME := demo

include $(CURDIR)/../../include.mk

test-k: demo-spec.kprove

clean:
	rm -rf $(KOMPILED)

.PHONY: test-k test golden clean %.test %.krun
