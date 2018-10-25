TOP != git rev-parse --show-toplevel
include $(TOP)/include.mk

KOMPILED := list-unify-4-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): list-unify-4.k $(KOMPILE_TARGETS)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module list-unify-4

%.list-unify-4.kore: %.list-unify-4 $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.list-unify-4 $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.list-unify-4 $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test 

test-k: tests/1.test tests/2.test tests/3.test 

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.list-unify-4.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
