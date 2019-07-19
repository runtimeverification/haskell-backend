include $(CURDIR)/../../../../working/include.mk

KOMPILED = path-kompiled
DEFINITION = $(KOMPILED)/definition.kore

$(DEFINITION): path.k
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module PATH

%.krun: %.path $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.kprove: %.k $(DEFINITION) $(KORE_EXEC)
	$(KPROVE) $(KPROVE_OPTS) -d . -m PATH $<

%.knotprove: %.k $(DEFINITION) $(KORE_EXEC)
	$(KPROVE) $(KPROVE_OPTS) -d . -m PATH $<

%.krepl: %.k $(DEFINITION) $(KORE_REPL)
	!$(KPROVE) $(KPROVE_REPL_OPTS) -d . -m PATH $<

%.output: %.path $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.search.final.output: %.path $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final \
		$(foreach pat, $(wildcard $*.search.pattern), --pattern "$$(cat $(pat))")

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

all_tests := $(k_tests)
k_tests :=
not_prove_tests := \
	all-path-a-c-b-d-spec
prove_tests := \
	all-path-a-c-spec \
	all-path-b-d-spec \

test: $(foreach test, $(all_tests), tests/$(test).test)

test-k: $(foreach test, $(k_tests), tests/$(test).test) \
	test-prove \
	test-unprove

test-prove: $(foreach test, $(prove_tests), provable/$(test).kprove)

#test-unprove: $(foreach test, $(not_prove_tests), notprovable/$(test).knotprove)

golden: $(foreach test, $(all_tests), tests/$(test).output.golden)

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
