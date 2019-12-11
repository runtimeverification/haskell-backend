DEFINITION_NAME := demo

include $(CURDIR)/../../include.mk

test: tests/1.test tests/2.test tests/3.test tests/4.test

test-k: tests/1.test tests/2.test tests/3.test tests/4.test

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden tests/4.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
