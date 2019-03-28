DEFINITION_NAME := search

include $(CURDIR)/../include.mk

%.search.star.unreachable.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-all --pattern '<k> unreachable </k>'

%.search.plus.unreachable.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-or-more-steps --pattern '<k> unreachable </k>'

%.search.one.unreachable.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-step --pattern '<k> unreachable </k>'

%.search.final.unreachable.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final --pattern '<k> unreachable </k>'

%.search.star.initial.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-all --pattern '<k> initial </k>'

%.search.plus.initial.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-or-more-steps --pattern '<k> initial </k>'

%.search.one.initial.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-step --pattern '<k> initial </k>'

%.search.final.initial.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final --pattern '<k> initial </k>'

test: test-k

test-k: \
	tests/initial.search.star.test \
	tests/initial.search.plus.test \
	tests/initial.search.one.test \
	tests/initial.search.final.test \
	tests/initial.search.star.unreachable.test \
	tests/initial.search.plus.unreachable.test \
	tests/initial.search.one.unreachable.test \
	tests/initial.search.final.unreachable.test \
	tests/initial.search.star.initial.test \
	tests/initial.search.plus.initial.test \
	tests/initial.search.one.initial.test \
	tests/initial.search.final.initial.test

golden: \
	tests/initial.search.star.output.golden \
	tests/initial.search.plus.output.golden \
	tests/initial.search.one.output.golden \
	tests/initial.search.final.output.golden \
	tests/initial.search.star.unreachable.output.golden \
	tests/initial.search.plus.unreachable.output.golden \
	tests/initial.search.one.unreachable.output.golden \
	tests/initial.search.final.unreachable.output.golden \
	tests/initial.search.star.initial.output.golden \
	tests/initial.search.plus.initial.output.golden \
	tests/initial.search.one.initial.output.golden \
	tests/initial.search.final.initial.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
