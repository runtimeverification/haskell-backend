TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := imp-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): imp.k $(K)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module IMP

%.imp.kore: %.imp $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.krun: %.imp $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.kprove: %.k $(DEFINITION) $(K) $(KORE_EXEC)
	$(KPROVE) $(KPROVE_OPTS) -d . -m VERIFICATION $<

%.output: %.imp $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.search.final.output: %.imp $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final \
		$(foreach pat, $(wildcard $*.search.pattern), --pattern "$$(cat $(pat))")

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

all_tests := \
	collatz \
	impossible-branch.search.final \
	max-symbolic.search.final \
	primes \
	sum
k_tests := \
	impossible-branch.search.final \
	sum
prove_tests := \
	add-spec \
	max-spec \
	sum-spec \

test: $(foreach test, $(all_tests), tests/$(test).test)

test-k: $(foreach test, $(k_tests), tests/$(test).test) \
	test-prove

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)

golden: $(foreach test, $(all_tests), tests/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.imp.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
