TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := imp-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): imp.k $(KOMPILE)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module IMP

%.imp.kore: %.imp $(DEFINITION) $(KRUN) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.krun: %.imp $(DEFINITION) $(KRUN) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.kprove: %.k $(DEFINITION) $(KPROVE) $(KORE_EXEC)
	$(KPROVE) $(KPROVE_OPTS) -d . -m VERIFICATION $<

%.output: %.k $(DEFINITION) $(KRUN) $(KORE_EXEC)
	$(KPROVE) $(KPROVE_OPTS) -d . -m VERIFICATION $< --output-file $@

%.search.final.output: %.imp $(DEFINITION) $(KRUN) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final \
		$(foreach pat, $(wildcard $*.search.pattern), --pattern "$$(cat $(pat))")

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

prove_tests := \
	sum-spec

test: test-k

test-k: test-prove

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)

golden: $(foreach test, $(prove_tests), prove/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) prove/*.imp.kore prove/*.output

.PHONY: test-k test test-prove golden clean %.test %.krun
