TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := list-map-unify-concrete-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): list-map-unify-concrete.k $(KOMPILE)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module list-map-unify-concrete

%.list-map-unify-concrete.kore: %.list-map-unify-concrete $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.list-map-unify-concrete $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.list-map-unify-concrete $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test

test-k: tests/1.test tests/2.test tests/3.test

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.list-map-unify-concrete.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
