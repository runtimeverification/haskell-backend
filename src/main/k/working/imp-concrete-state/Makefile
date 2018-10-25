TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := imp-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): imp.k $(KOMPILE_TARGETS)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module IMP

%.imp.kore: %.imp $(DEFINITION) $(K)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.imp $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.imp $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/sum.test tests/primes.test tests/collatz.test tests/max-symbolic.test

test-k: tests/sum.test

golden: tests/sum.output.golden tests/primes.output.golden tests/collatz.output.golden tests/max-symbolic.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.imp.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
