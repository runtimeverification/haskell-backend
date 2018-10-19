TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := demo-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): demo.k $(KOMPILE_TARGETS)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module DEMO

%.imp.kore: %.demo $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.demo $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.demo $(DEFINITION) $(KRUN_TARGETS)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/Nat.test tests/NatList.test tests/Truth.test

test-k: test

golden: tests/Nat.output.golden tests/NatList.output.golden tests/Truth.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.imp.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
