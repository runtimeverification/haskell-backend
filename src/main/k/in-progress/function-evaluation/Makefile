TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := eval-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): eval.k $(KOMPILE)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module EVAL

%.eval.kore: %.eval $(DEFINITION) $(KRUN) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.output: %.eval $(DEFINITION) $(KRUN) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.search.final.output: %.eval $(DEFINITION) $(KRUN) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final

%.krun: %.eval $(DEFINITION) $(KRUN) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

all_tests := isOne-One \
             isOne-symNat \
             isZero-symNat \
             lenInt-symNatList \
             lenNat-symNatList \
             Pred-symNat \
             Pred-Zero \
             succ-symInt \
             Succ-Zero-plus-symNat \
             symNat-plus-symNat \
             Zero-plus-symNat \
# k_tests := sum

test: $(foreach test, $(all_tests), tests/$(test).test)

test-k: $(foreach test, $(k_tests), tests/$(test).test)

golden: $(foreach test, $(all_tests), tests/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.eval.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
