DEFINITION_NAME := abc

include $(CURDIR)/../include.mk

prove_tests := b-spec c-spec

test: test-k

test-k: test-prove

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)

golden: $(foreach test, $(all_tests), tests/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
