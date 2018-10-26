TOP != git rev-parse --show-toplevel
include $(TOP)/include.mk

KOMPILED := map-unify-concrete-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): map-unify-concrete.k $(K)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module map-unify-concrete

%.map-unify-concrete.kore: %.map-unify-concrete $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.map-unify-concrete $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.map-unify-concrete $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test tests/4.test tests/5.test

test-k: tests/1.test tests/2.test tests/3.test tests/4.test tests/5.test

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden tests/4.output.golden tests/5.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.map-unify-concrete.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
