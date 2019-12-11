ifeq ($(origin TOP), undefined)
	TOP = $(shell git rev-parse --show-toplevel)
endif

include $(TOP)/include.mk

DEF ?= test
EXT ?= $(DEF)

DEF_DIR ?= .
TEST_DIR ?= .

DIFF ?= diff -u

KOMPILED := $(TEST_DIR)/$(DEF)-kompiled
DEF_KORE := $(KOMPILED)/definition.kore

KPROVE_MODULE ?= VERIFICATION

TESTS ?= $(wildcard $(TEST_DIR)/*.$(EXT))
SEARCH_TESTS ?= \
	$(wildcard $(TEST_DIR)/*.$(EXT).search-*) \
	$(wildcard $(TEST_DIR)/*.$(EXT).pattern-search-*)
PROOF_TESTS ?= $(wildcard $(TEST_DIR)/*-spec.k)
BMC_TESTS ?= $(wildcard $(TEST_DIR)/*-spec.bmc.k)

$(DEF_KORE): $(DEF).k $(K) $(KOMPILE)
	rm -fr $(KOMPILED)
	$(KOMPILE) $(KOMPILE_OPTS) $< -d $(DEF_DIR)

# From make 3.82 news: http://cvs.savannah.gnu.org/viewvc/*checkout*/make/make/NEWS?revision=2.120
# * WARNING: Backward-incompatibility!
#   The pattern-specific variables and pattern rules are now applied in the
#   shortest stem first order instead of the definition order (variables
#   and rules with the same stem length are still applied in the definition
#   order). This produces the usually-desired behavior where more specific
#   patterns are preferred. To detect this feature search for 'shortest-stem'
#   in the .FEATURES special variable.

%.$(EXT).out: %.$(EXT) $(DEF_KORE) $(KORE_EXEC) $(K) $(KRUN)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) $< --output-file $@
	$(DIFF) $@.golden $@

%.golden: DIFF = true
%.golden: %
	cp $< $@

%-spec.k.out: %-spec.k $(DEF_KORE) $(KORE_EXEC) $(K) $(KPROVE)
	$(KPROVE) $(KPROVE_OPTS) -d $(DEF_DIR) -m $(KPROVE_MODULE) $< --output-file $@ || true
	$(DIFF) $@.golden $@

%.merge.out: %.merge $(DEF_KORE) $(KORE_EXEC)
	$(KORE_EXEC) $(DEF_KORE) --module $(MODULE) --merge-rules $< --output $@
	$(DIFF) $@.golden $@

%.$(EXT).search-final.out: %.$(EXT).search-final $(DEF_KORE) $(KORE_EXEC) $(K) $(KRUN)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) $< --output-file $@ --search-final
	$(DIFF) $@.golden $@

%.$(EXT).search-all.out: %.$(EXT).search-all $(DEF_KORE) $(KORE_EXEC) $(K) $(KRUN)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) $< --output-file $@ --search-all
	$(DIFF) $@.golden $@

%.$(EXT).search-one-or-more-steps.out: %.$(EXT).search-one-or-more-steps $(DEF_KORE) $(KORE_EXEC) $(K) $(KRUN)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) $< --output-file $@ --search-one-or-more-steps
	$(DIFF) $@.golden $@

%.$(EXT).search-one-step.out: %.$(EXT).search-one-step $(DEF_KORE) $(KORE_EXEC) $(K) $(KRUN)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) $< --output-file $@ --search-one-step
	$(DIFF) $@.golden $@

%.$(EXT).pattern-search-final.out: %.$(EXT).pattern-search-final $*.k $(DEF_KORE) $(KORE_EXEC) $(K) $(KRUN)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) $< --output-file $@ --search-final --pattern "$$(cat $*.)"
	$(DIFF) $@.golden $@

%.$(EXT).pattern-search-all.out: %.$(EXT).pattern-search-all $*.k $(DEF_KORE) $(KORE_EXEC) $(K) $(KRUN)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) $< --output-file $@ --search-all --pattern "$$(cat $*.k)"
	$(DIFF) $@.golden $@

%.$(EXT).pattern-search-one-step.out: %.$(EXT).pattern-search-one-step $*.k $(DEF_KORE) $(KORE_EXEC) $(K) $(KRUN)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) $< --output-file $@ --search-one-step --pattern "$$(cat $*.k)"
	$(DIFF) $@.golden $@

%.$(EXT).pattern-search-one-or-more-steps.out: %.$(EXT).pattern-search-one-or-more-steps $*.k $(DEF_KORE) $(KORE_EXEC) $(K) $(KRUN)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) $< --output-file $@ --search-one-or-more-steps --pattern "$$(cat $*.k)"
	$(DIFF) $@.golden $@

%-spec.k.repl.out: %-spec.k $(DEF_KORE) $(KORE_EXEC) $(K) $(KPROVE)
	$(KPROVE) $(KPROVE_REPL_OPTS) -d $(DEF_DIR) -m $(KPROVE_MODULE) $< --output-file $@ || true
	$(DIFF) $@.golden $@

%-spec.k.repl-script.out: KPROVE_REPL_OPTS = --haskell-backend-command "$(KORE_REPL) -r --repl-script $<.repl"
%-spec.k.repl-script.out: %-spec.k $(DEF_KORE) $(KORE_EXEC) $(K) $(KPROVE)
	$(KPROVE) $(KPROVE_REPL_OPTS) -d $(DEF_DIR) -m $(KPROVE_MODULE) $< --output-file $@ || true
	$(DIFF) $@.golden $@

%-spec.bmc.out: %-spec.k $(DEF_KORE) $(KORE_EXEC) $(K) $(KBMC)
	$(KBMC) $(KPROVE_OPTS) --debug --raw-spec $< -d $(DEF_DIR) -m $(MODULE) --depth $(KBMC_DEPTH) --output-file $@ || exit 0

test: test-k

OUTS = $(foreach TEST, $(TESTS) $(SEARCH_TESTS) $(PROOF_TESTS) $(BMC_TESTS), $(TEST).out)

test-k: $(OUTS)

golden: $(foreach OUT, $(OUTS), $(OUT).golden)

clean:
	rm -fr $(KOMPILED) $(TEST_DIR)/*.out

.PHONY: test-k test golden clean
