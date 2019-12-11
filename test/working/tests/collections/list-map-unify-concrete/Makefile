DEFINITION_NAME := list-map-unify-concrete

include $(CURDIR)/../../../include.mk

# TODO: These files should specify just the names of different test-sets and let `include.mk` do the rest.

test: tests/1.test tests/2.test tests/3.test

test-k: tests/1.test tests/2.test tests/3.test

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
