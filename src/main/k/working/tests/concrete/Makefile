DEFINITION_NAME := concrete

include $(CURDIR)/../../include.mk

test: tests/1.test tests/2.test

test-k: test

golden: tests/1.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
