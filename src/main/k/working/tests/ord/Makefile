TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := ord-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): ord.k $(K)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module ord

%.ord.kore: %.ord $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.ord $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.ord $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test

test-k: tests/1.test tests/2.test

golden: tests/1.output.golden tests/2.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.ord.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
