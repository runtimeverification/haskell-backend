TOP != git rev-parse --show-toplevel
include $(TOP)/include.mk

KOMPILED := list-unify-first-elem-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): list-unify-first-elem.k $(KOMPILE_TARGETS)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module list-unify-first-elem

%.list-unify-first-elem.kore: %.list-unify-first-elem $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.list-unify-first-elem $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.list-unify-first-elem $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test 

test-k: tests/1.test tests/2.test tests/3.test 

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.list-unify-first-elem.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
