include $(CURDIR)/../../../include.mk

KOMPILED := map-unify-framing-variable-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): map-unify-framing-variable.k
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module MAP-UNIFY-FRAMING-VARIABLE

%.output: %.map-unify-framing-variable $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.map-unify-framing-variable $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test

test-k: tests/1.test tests/2.test tests/3.test

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
