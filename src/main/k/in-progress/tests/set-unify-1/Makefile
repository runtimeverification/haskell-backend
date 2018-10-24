TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := set-unify-1-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): set-unify-1.k $(KOMPILE_TARGETS)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module set-unify-1

%.set-unify-1.kore: %.set-unify-1 $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.set-unify-1 $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.set-unify-1 $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test 

test-k: tests/1.test tests/2.test tests/3.test 

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.set-unify-1.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
