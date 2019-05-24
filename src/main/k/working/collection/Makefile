DEFINITION_NAME := harness

include $(CURDIR)/../include.mk

all_tests := \
	test-map-idem \
	test-set-idem \

k_tests := \
	test-map-idem \
	test-set-idem \

prove_tests := \
	map-spec \
	set-spec \

test: $(foreach test, $(all_tests), tests/$(test).test)

test-k: $(foreach test, $(k_tests), tests/$(test).test) \
	test-prove

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)

golden: $(foreach test, $(all_tests), tests/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
