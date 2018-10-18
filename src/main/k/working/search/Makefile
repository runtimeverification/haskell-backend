TOP != git rev-parse --show-toplevel
include $(TOP)/include.mk

KOMPILED := search-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): search.k $(KOMPILE_TARGETS)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module SEARCH

%.search.kore: %.search $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.star.output: %.search $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-all

%.plus.output: %.search $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-or-more-steps

%.one.output: %.search $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-step

%.final.output: %.search $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final

%.krun: %.search $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: test-k

test-k: tests/initial.star.test tests/initial.plus.test tests/initial.one.test tests/initial.final.test

golden: tests/initial.star.output.golden tests/initial.plus.output.golden tests/initial.one.output.golden tests/initial.final.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.search.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
