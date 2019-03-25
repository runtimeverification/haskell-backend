include $(CURDIR)/../../../include.mk

KOMPILED := map-lookup-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): map-lookup.k
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module MAP-LOOKUP

%.output: %.map-lookup $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.map-lookup $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test

test-k: tests/1.test

golden: tests/1.output.golden tests/2.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
