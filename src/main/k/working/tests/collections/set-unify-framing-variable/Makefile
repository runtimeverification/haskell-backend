include $(CURDIR)/../../../include.mk

KOMPILED := set-unify-framing-variable-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): set-unify-framing-variable.k
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module SET-UNIFY-FRAMING-VARIABLE

%.output: %.set-unify-framing-variable $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.set-unify-framing-variable $(DEFINITION) $(KORE_EXEC)
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
