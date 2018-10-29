TOP := $(shell git rev-parse --show-toplevel)
include $(TOP)/include.mk

KOMPILED := search-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): search.k $(K)
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module SEARCH

%.search.kore: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --dry-run

%.star.output: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-all

%.plus.output: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-or-more-steps

%.one.output: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-step

%.final.output: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final

%.star.unreachable.output: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-all --pattern '<k> unreachable </k>'

%.plus.unreachable.output: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-or-more-steps --pattern '<k> unreachable </k>'

%.one.unreachable.output: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-step --pattern '<k> unreachable </k>'

%.final.unreachable.output: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final --pattern '<k> unreachable </k>'

%.star.initial.output: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-all --pattern '<k> initial </k>'

%.plus.initial.output: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-or-more-steps --pattern '<k> initial </k>'

%.one.initial.output: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-step --pattern '<k> initial </k>'

%.final.initial.output: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final --pattern '<k> initial </k>'

%.krun: %.search $(DEFINITION) $(K) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: test-k

test-k: \
	tests/initial.star.test \
	tests/initial.plus.test \
	tests/initial.one.test \
	tests/initial.final.test \
	tests/initial.star.unreachable.test \
	tests/initial.plus.unreachable.test \
	tests/initial.one.unreachable.test \
	tests/initial.final.unreachable.test \
	tests/initial.star.initial.test \
	tests/initial.plus.initial.test \
	tests/initial.one.initial.test \
	tests/initial.final.initial.test

golden: \
	tests/initial.star.output.golden \
	tests/initial.plus.output.golden \
	tests/initial.one.output.golden \
	tests/initial.final.output.golden \
	tests/initial.star.unreachable.output.golden \
	tests/initial.plus.unreachable.output.golden \
	tests/initial.one.unreachable.output.golden \
	tests/initial.final.unreachable.output.golden \
	tests/initial.star.initial.output.golden \
	tests/initial.plus.initial.output.golden \
	tests/initial.one.initial.output.golden \
	tests/initial.final.initial.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.search.kore tests/*.output

.PHONY: test-k test golden clean %.test %.krun
