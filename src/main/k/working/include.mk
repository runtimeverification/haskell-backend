ifeq ($(origin TOP), undefined)
	TOP = $(shell git rev-parse --show-toplevel)
endif

include $(TOP)/include.mk

KOMPILED := $(DEFINITION_NAME)-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION) : $(DEFINITION_NAME).k
	$(KOMPILE) $(KOMPILE_OPTS) $<

%.krun: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.kprove: %.k $(DEFINITION) $(KORE_EXEC)
	$(KPROVE) $(KPROVE_OPTS) -d . -m VERIFICATION $<

%.search.final.output: %.$(DEFINITION) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final

%.krepl: %.k $(DEFINITION) $(KORE_EXEC)
	$(KPROVE) $(KPROVE_REPL_OPTS) -d . -m VERIFICATION $<

%.search.star.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-all

%.search.plus.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-or-more-steps

%.search.one.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-step

%.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

.PHONY: test-k test golden clean %.test %.krun
