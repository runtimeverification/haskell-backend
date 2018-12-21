TOP != git rev-parse --show-toplevel
include $(TOP)/include.mk

KOMPILED := eqtest-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): eqtest.k $(K)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module eqtest

%.eqtest.kore: %.eqtest $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.eqtest $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.eqtest $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test tests/4.test

test-k: tests/1.test tests/2.test tests/3.test tests/4.test

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden tests/4.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.eqtest.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
