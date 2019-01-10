TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := map-lookup-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): map-lookup.k $(KOMPILE)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module MAP-LOOKUP

%.map-lookup.kore: %.map-lookup $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.map-lookup $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.map-lookup $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test

test-k: tests/1.test

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden tests/4.output.golden tests/5.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.map-lookup.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
