TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := strict-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): strict.k $(KOMPILE)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module STRICT

%.strict.kore: %.strict $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.strict $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.strict $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/10.test tests/g2.test tests/g21.test tests/g3.test tests/seq.test tests/nd.test

test-k: tests/1.test tests/10.test tests/g2.test tests/g21.test tests/g3.test tests/seq.test tests/nd.test

golden: tests/1.output.golden tests/10.output.golden tests/g2.output.golden tests/g21.output.golden tests/g3.output.golden tests/seq.output.golden tests/nd.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.strict.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
