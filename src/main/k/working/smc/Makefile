include $(CURDIR)/../include.mk

KOMPILED = smc-kompiled
DEFINITION = $(KOMPILED)/definition.kore

$(DEFINITION): smc.k
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module SMC-SYNTAX

%.krun: %.smc $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.kprove: %.k $(DEFINITION) $(KORE_EXEC)
	$(KPROVE) $(KPROVE_OPTS) -d . -m VERIFICATION $<

%.output: %.smc $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.search.final.output: %.smc $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final \
		$(foreach pat, $(wildcard $*.search.pattern), --pattern "$$(cat $(pat))")

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

all_tests := \
	collatz \
	primes \
	sum
k_tests := \
	sum
prove_tests := \
	add-spec \
	max-spec \
	sum-spec \
	double-sum-spec \
	add-stack-spec \
	max-stack-spec \
	sum-stack-spec \

test: $(foreach test, $(all_tests), tests/$(test).test)

test-k: $(foreach test, $(k_tests), tests/$(test).test) \
	test-prove

test-prove: $(foreach test, $(prove_tests), prove/$(test).kprove)

golden: $(foreach test, $(all_tests), tests/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
