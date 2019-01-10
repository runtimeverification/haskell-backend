TOP != git rev-parse --show-toplevel
include $(TOP)/include.mk

KOMPILED := set-unify-concrete-2-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): set-unify-concrete-2.k $(KOMPILE)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module set-unify-concrete-2

%.set-unify-concrete-2.kore: %.set-unify-concrete-2 $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.set-unify-concrete-2 $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.set-unify-concrete-2 $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test

test-k: tests/1.test tests/2.test tests/3.test

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.set-unify-concrete-2.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
