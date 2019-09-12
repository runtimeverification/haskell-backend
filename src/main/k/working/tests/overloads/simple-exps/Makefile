DEFINITION_NAME := simple-exps

include $(CURDIR)/../../../include.mk

test: tests/1.test

golden: tests/1.output.golden

test-k: test

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
