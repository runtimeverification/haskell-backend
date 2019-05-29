DEFINITION_NAME := overloaded-productions

include $(CURDIR)/../include.mk

prove_tests := test1-spec

test-prove: $(prove_tests:=.kprove)

test: test-prove

test-k: test-prove

golden: $(foreach test, $(all_tests), tests/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
