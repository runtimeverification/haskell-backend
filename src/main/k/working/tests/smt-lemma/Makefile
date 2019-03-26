include $(CURDIR)/../../include.mk

KOMPILED := test-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION): test.k
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module TEST

%.output: %.t $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.t $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.kprove: %.k $(DEFINITION) $(KORE_EXEC)
	$(KPROVE) $(KPROVE_OPTS) -d . -m TEST $<

%.krepl: %.k $(DEFINITION) $(KORE_EXEC)
	$(KPROVE) $(KPROVE_REPL_OPTS) -d . -m TEST $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test

test-prove: prove/1-spec.kprove

test-k: tests/1.test tests/2.test tests/3.test \
    	test-prove

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden tests/4.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun test-prove
