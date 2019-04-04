DEFINITION_NAME := imp

include $(CURDIR)/../include.mk

all_tests := collatz max-symbolic.search.final primes sum
k_tests := sum

test: $(foreach test, $(all_tests), tests/$(test).test)

test-k: $(foreach test, $(k_tests), tests/$(test).test)

golden: $(foreach test, $(all_tests), tests/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
