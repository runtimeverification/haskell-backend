TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := imp-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): imp.k $(K)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module IMP

%.imp.kore: %.imp $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.krun: %.imp $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.output: %.imp $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.search.final.output: %.imp $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

all_tests := \
	collatz impossible-branch.search.final max-symbolic.search.final primes sum
k_tests := impossible-branch.search.final max-symbolic.search.final sum

test: $(foreach test, $(all_tests), tests/$(test).test)

test-k: $(foreach test, $(k_tests), tests/$(test).test)

golden: $(foreach test, $(all_tests), tests/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.imp.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
