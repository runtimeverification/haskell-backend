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
	$(wildcard $(TEST_DIR)/*.search.*.$(EXT)) \
	$(wildcard $(TEST_DIR)/*.search-pattern.*.$(EXT))
PROOF_TESTS ?= \
	$(wildcard $(TEST_DIR)/*-spec.k) \
	$(wildcard $(TEST_DIR)/*-spec.repl.k) \
	$(wildcard $(TEST_DIR)/*-spec.repl-script.k)
BMC_TESTS ?= $(wildcard $(TEST_DIR)/*-spec.bmc.k)

OUTS = $(foreach TEST, $(TESTS) $(SEARCH_TESTS) $(PROOF_TESTS) $(BMC_TESTS), $(TEST).out)

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

%.merge.out: %.merge $(DEF_KORE) $(KORE_EXEC)
	$(KORE_EXEC) $(DEF_KORE) --module $(MODULE) --merge-rules $< --output $@
	$(DIFF) $@.golden $@

### SEARCH

%.search.final.$(EXT).out: %.search.final.$(EXT) $(DEF_KORE) $(KORE_EXEC) $(K)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) \
		--search-final \
		$< --output-file $@
	$(DIFF) $@.golden $@

%.search.star.$(EXT).out: %.search.star.$(EXT) $(DEF_KORE) $(KORE_EXEC) $(K)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) \
		--search-all \
		$< --output-file $@
	$(DIFF) $@.golden $@

%.search.one.$(EXT).out: %.search.one.$(EXT) $(DEF_KORE) $(KORE_EXEC) $(K)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) \
		--search-one-step \
		$< --output-file $@
	$(DIFF) $@.golden $@

%.search.plus.$(EXT).out: %.search.plus.$(EXT) $(DEF_KORE) $(KORE_EXEC) $(K)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) \
		--search-one-step \
		$< --output-file $@
	$(DIFF) $@.golden $@

%.search-pattern.final.$(EXT).out: %.search-pattern.final.$(EXT) $(DEF_KORE) $(KORE_EXEC) $(K)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) \
		--search-final --pattern "$$(cat $*.search-pattern.k)" \
		$< --output-file $@
	$(DIFF) $@.golden $@

%.search-pattern.star.$(EXT).out: %.search-pattern.star.$(EXT) $(DEF_KORE) $(KORE_EXEC) $(K)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) \
		--search-all --pattern "$$(cat $*.search-pattern.k)" \
		$< --output-file $@
	$(DIFF) $@.golden $@

%.search-pattern.one.$(EXT).out: %.search-pattern.one.$(EXT) $(DEF_KORE) $(KORE_EXEC) $(K)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) \
		--search-one-step --pattern "$$(cat $*.search-pattern.k)" \
		$< --output-file $@
	$(DIFF) $@.golden $@

%.search-pattern.plus.$(EXT).out: %.search-pattern.plus.$(EXT) $(DEF_KORE) $(KORE_EXEC) $(K)
	$(KRUN) $(KRUN_OPTS) -d $(DEF_DIR) \
		--search-one-or-more-steps --pattern "$$(cat $*.search-pattern.k)" \
		$< --output-file $@
	$(DIFF) $@.golden $@

### PROVE

%-spec.k.out: %-spec.k $(DEF_KORE) $(KORE_EXEC) $(K)
	$(KPROVE) $(KPROVE_OPTS) -d $(DEF_DIR) -m $(KPROVE_MODULE) \
		$< --output-file $@ \
		|| true
	$(DIFF) $@.golden $@

%-spec.repl.k.out: %-spec.k $(DEF_KORE) $(KORE_EXEC) $(K)
	$(KPROVE) $(KPROVE_REPL_OPTS) -d $(DEF_DIR) -m $(KPROVE_MODULE) \
		$< --output-file $@ \
		|| true
	$(DIFF) $@.golden $@

%-spec.repl-script.k.out: KPROVE_REPL_OPTS = --haskell-backend-command "$(KORE_REPL) -r --repl-script $<.repl"
%-spec.repl-script.k.out: %-spec.k $(DEF_KORE) $(KORE_EXEC) $(K) $(KPROVE)
	$(KPROVE) $(KPROVE_REPL_OPTS) -d $(DEF_DIR) -m $(KPROVE_MODULE) \
		$< --output-file $@ \
		|| true
	$(DIFF) $@.golden $@

### BMC

%-spec.bmc.out: %-spec.bmc.k $(DEF_KORE) $(KORE_EXEC) $(K) $(KBMC)
	$(KBMC) $(KPROVE_OPTS) -d $(DEF_DIR) -m $(MODULE) \
		--debug --raw-spec --depth $(KBMC_DEPTH) \
		$< --output-file $@ \
		|| exit 0
	$(DIFF) $@.golden $@

### TARGETS

test: test-k

test-k: $(OUTS)

golden: $(foreach OUT, $(OUTS), $(OUT).golden)

clean:
	rm -fr $(KOMPILED) $(TEST_DIR)/*.out

.PHONY: test-k test golden clean
