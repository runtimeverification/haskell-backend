DEFINITION_NAME := map-lookup

include $(CURDIR)/../../../include.mk

test: tests/1.test

test-k: tests/1.test

golden: tests/1.output.golden tests/2.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
