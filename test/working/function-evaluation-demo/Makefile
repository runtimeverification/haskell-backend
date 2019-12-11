DEFINITION_NAME := demo

include $(CURDIR)/../include.mk

test: tests/Nat.test tests/NatList.test tests/Truth.test

test-k: test

golden: tests/Nat.output.golden tests/NatList.output.golden tests/Truth.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
