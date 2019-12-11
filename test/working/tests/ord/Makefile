DEFINITION_NAME := ord

include $(CURDIR)/../../include.mk

test: tests/1.test tests/2.test

test-k: tests/1.test tests/2.test

golden: tests/1.output.golden tests/2.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
