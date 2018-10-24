TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := list-unify-concrete-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): list-unify-concrete.k $(KOMPILE_TARGETS)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module list-unify-concrete

%.list-unify-concrete.kore: %.list-unify-concrete $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.list-unify-concrete $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.list-unify-concrete $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test tests/4.test tests/5.test

test-k: tests/1.test tests/2.test tests/3.test tests/4.test tests/5.test

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden tests/4.output.golden tests/5.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.list-unify-concrete.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
