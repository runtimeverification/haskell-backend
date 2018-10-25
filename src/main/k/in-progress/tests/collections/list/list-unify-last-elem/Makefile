TOP != git rev-parse --show-toplevel
include $(TOP)/include.mk

KOMPILED := list-unify-last-elem-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): list-unify-last-elem.k $(KOMPILE_TARGETS)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module list-unify-last-elem

%.list-unify-last-elem.kore: %.list-unify-last-elem $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.list-unify-last-elem $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.list-unify-last-elem $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test 

test-k: tests/1.test tests/2.test tests/3.test 

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.list-unify-last-elem.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
