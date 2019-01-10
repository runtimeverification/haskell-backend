TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := list-unify-framing-variable-left-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): list-unify-framing-variable-left.k $(KOMPILE)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module LIST-UNIFY-FRAMING-VARIABLE-LEFT

%.list-unify-framing-variable-left.kore: %.list-unify-framing-variable-left $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.list-unify-framing-variable-left $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.list-unify-framing-variable-left $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test

test-k: tests/1.test tests/2.test tests/3.test

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.list-unify-framing-variable-left.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
