ifeq ($(origin TOP), undefined)
	TOP = $(shell git rev-parse --show-toplevel)
endif

include $(TOP)/include.mk

KOMPILED := $(DEFINITION_NAME)-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION) : $(DEFINITION_NAME).k
	$(KOMPILE) $(KOMPILE_OPTS) $<

# From make 3.82 news: http://cvs.savannah.gnu.org/viewvc/*checkout*/make/make/NEWS?revision=2.120
# * WARNING: Backward-incompatibility!
#   The pattern-specific variables and pattern rules are now applied in the
#   shortest stem first order instead of the definition order (variables
#   and rules with the same stem length are still applied in the definition
#   order). This produces the usually-desired behavior where more specific
#   patterns are preferred. To detect this feature search for 'shortest-stem'
#   in the .FEATURES special variable.

%.krun: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.kprove: %.k $(DEFINITION) $(KORE_EXEC)
	$(KPROVE) $(KPROVE_OPTS) -d . -m VERIFICATION $<

%.kmerge: %.merge $(DEFINITION) $(KORE_EXEC)
	$(KORE_EXEC) --definition $(DEFINITION) --merge-rules $<

%.search.final.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final

%.psearch.final.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-final \
	    $(foreach pat, $(wildcard $*.search.pattern), --pattern "$$(cat $(pat))")

%.krepl: %.k $(DEFINITION) $(KORE_REPL)
	$(KPROVE) $(KPROVE_REPL_OPTS) -d . -m VERIFICATION $<

%.kscript: % $(DEFINITION) $(KORE_REPL)
	$(KPROVE) --haskell-backend-command "$(KORE_REPL) -r --repl-script $<" -d ../.. -m VERIFICATION $(SPEC_FILE)

%.search.star.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-all

%.search.plus.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-or-more-steps

%.search.one.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ --search-one-step

%.kbmc.output: $(DEFINITION) $(KORE_EXEC)
	$(KBMC) $(KPROVE_OPTS) --debug --raw-spec $(basename $*).k -d . -m VERIFICATION --depth $(subst ., ,$(suffix $*)) --output-file $@ || exit 0

%.output: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.merge-output: %.merge $(DEFINITION) $(KORE_EXEC)
	$(KORE_EXEC) $(DEFINITION) --module $(MODULE_NAME) --merge-rules $< --output $@

%.repl.output: % $(DEFINITION) $(KORE_REPL)
	$(KPROVE) --haskell-backend-command "$(KORE_REPL) -r --repl-script $<" -d ../.. -m VERIFICATION $(SPEC_FILE) --output-file $@

%.test: %.output
	diff -u $<.golden $<

%.merge-test: %.merge-output
	diff -u $(basename $<).merge-golden $<

%.output.golden: %.output
	mv $< $<.golden

%.merge-golden: %.merge-output
	mv $< $(basename $<).merge-golden

.PHONY: test-k test golden clean %.test %.krun
