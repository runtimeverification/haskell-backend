TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := list-unify-any-elem-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): list-unify-any-elem.k $(KOMPILE)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module LIST-UNIFY-ANY-ELEM

%.list-unify-any-elem.kore: %.list-unify-any-elem $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.list-unify-any-elem $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.list-unify-any-elem $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test

test-k: tests/1.test tests/2.test tests/3.test

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.list-unify-any-elem.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
