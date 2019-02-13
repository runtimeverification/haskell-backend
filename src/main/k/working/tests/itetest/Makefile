include $(CURDIR)/../../include.mk

KOMPILED := itetest-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): itetest.k
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module ITETEST

%.output: %.itetest $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.itetest $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test

test-k: tests/1.test

golden: tests/1.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
