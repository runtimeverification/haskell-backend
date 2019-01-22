include $(CURDIR)/../include.mk

KOMPILED := imp-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): imp.k
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module IMP

%.output: %.imp $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.search.final.output: %.imp $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final

%.krun: %.imp $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

all_tests := collatz max-symbolic.search.final primes sum
k_tests := sum

test: $(foreach test, $(all_tests), tests/$(test).test)

test-k: $(foreach test, $(k_tests), tests/$(test).test)

golden: $(foreach test, $(all_tests), tests/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
