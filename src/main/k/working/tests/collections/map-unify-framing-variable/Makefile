TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := map-unify-framing-variable-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): map-unify-framing-variable.k $(KOMPILE_TARGETS)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module MAP-UNIFY-FRAMING-VARIABLE

%.map-unify-framing-variable.kore: %.map-unify-framing-variable $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.map-unify-framing-variable $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.map-unify-framing-variable $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test

test-k: tests/1.test tests/2.test tests/3.test

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.map-unify-framing-variable.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
