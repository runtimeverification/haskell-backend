DEFINITION_NAME := search

include $(CURDIR)/../include.mk

KOMPILED := $(DEFINITION_NAME)-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): $(DEFINITION_NAME).k
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module SEARCH

%.star.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-all

%.plus.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-or-more-steps

%.one.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-step

%.final.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final

%.star.unreachable.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-all --pattern '<k> unreachable </k>'

%.plus.unreachable.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-or-more-steps --pattern '<k> unreachable </k>'

%.one.unreachable.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-step --pattern '<k> unreachable </k>'

%.final.unreachable.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final --pattern '<k> unreachable </k>'

%.star.initial.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-all --pattern '<k> initial </k>'

%.plus.initial.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-or-more-steps --pattern '<k> initial </k>'

%.one.initial.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-step --pattern '<k> initial </k>'

%.final.initial.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final --pattern '<k> initial </k>'

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
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
