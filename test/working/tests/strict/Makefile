DEFINITION_NAME := strict

include $(CURDIR)/../../include.mk

test: tests/1.test tests/10.test tests/g2.test tests/g21.test tests/g3.test tests/seq.test tests/nd.test

test-k: tests/1.test tests/10.test tests/g2.test tests/g21.test tests/g3.test tests/seq.test tests/nd.test

golden: tests/1.output.golden tests/10.output.golden tests/g2.output.golden tests/g21.output.golden tests/g3.output.golden tests/seq.output.golden tests/nd.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
