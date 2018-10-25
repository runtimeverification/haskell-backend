TOP != git rev-parse --show-toplevel
include $(TOP)/include.mk

KOMPILED := list-unify-5-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): list-unify-5.k $(KOMPILE_TARGETS)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module list-unify-5

%.list-unify-5.kore: %.list-unify-5 $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.list-unify-5 $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.list-unify-5 $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test 

test-k: tests/1.test tests/2.test tests/3.test 

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.list-unify-5.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
