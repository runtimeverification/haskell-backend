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
TEST_DEPS = $(K) $(DEF_KORE) $(KORE_EXEC)

KPROVE_MODULE ?= VERIFICATION

TESTS ?= \
	$(wildcard $(TEST_DIR)/*.$(EXT)) \
	$(wildcard $(TEST_DIR)/*.search.*.$(EXT)) \
	$(wildcard $(TEST_DIR)/*.search-pattern.*.$(EXT)) \
	$(wildcard $(TEST_DIR)/*-spec.k) \
	$(wildcard $(TEST_DIR)/*-spec.repl.k) \
	$(wildcard $(TEST_DIR)/*-spec.repl-script.k) \
	$(wildcard $(TEST_DIR)/*-spec.bmc.k)

OUTS = $(foreach TEST, $(TESTS), $(TEST).out)

KOMPILE_OPTS += -d $(DEF_DIR)
KRUN_OPTS += -d $(DEF_DIR)
KPROVE_OPTS += -d $(DEF_DIR) -m $(KPROVE_MODULE)

$(DEF_KORE): $(DEF).k $(K)
	rm -fr $(KOMPILED)
	$(KOMPILE) $(KOMPILE_OPTS) $<

# From make 3.82 news: http://cvs.savannah.gnu.org/viewvc/*checkout*/make/make/NEWS?revision=2.120
# * WARNING: Backward-incompatibility!
#   The pattern-specific variables and pattern rules are now applied in the
#   shortest stem first order instead of the definition order (variables
#   and rules with the same stem length are still applied in the definition
#   order). This produces the usually-desired behavior where more specific
#   patterns are preferred. To detect this feature search for 'shortest-stem'
#   in the .FEATURES special variable.

%.$(EXT).out: %.$(EXT) $(TEST_DEPS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@
	$(DIFF) $@.golden $@

%.golden: DIFF = true
%.golden: %
	cp $< $@

%.merge.out: %.merge $(DEF_KORE) $(KORE_EXEC)
	$(KORE_EXEC) $(DEF_KORE) --module $(KORE_MODULE) --merge-rules $< --output $@
	$(DIFF) $@.golden $@

### SEARCH

%.search.final.$(EXT).out: KRUN_OPTS += --search-final
%.search.final.$(EXT).out: %.search.final.$(EXT) $(TEST_DEPS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@
	$(DIFF) $@.golden $@

%.search.star.$(EXT).out: KRUN_OPTS += --search-all
%.search.star.$(EXT).out: %.search.star.$(EXT) $(TEST_DEPS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@
	$(DIFF) $@.golden $@

%.search.one.$(EXT).out: KRUN_OPTS += --search-one-step
%.search.one.$(EXT).out: %.search.one.$(EXT) $(TEST_DEPS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@
	$(DIFF) $@.golden $@

%.search.plus.$(EXT).out: KRUN_OPTS += --search-one-or-more-steps
%.search.plus.$(EXT).out: %.search.plus.$(EXT) $(TEST_DEPS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@
	$(DIFF) $@.golden $@

PATTERN_OPTS = --pattern "$$(cat $*.search-pattern.k)"

%.search-pattern.final.$(EXT).out: KRUN_OPTS += --search-final $(PATTERN_OPTS)
%.search-pattern.final.$(EXT).out: %.search-pattern.final.$(EXT) $(TEST_DEPS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@
	$(DIFF) $@.golden $@

%.search-pattern.star.$(EXT).out: KRUN_OPTS += --search-all $(PATTERN_OPTS)
%.search-pattern.star.$(EXT).out: %.search-pattern.star.$(EXT) $(TEST_DEPS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ \
		--search-all --pattern "$$(cat $*.search-pattern.k)"
	$(DIFF) $@.golden $@

%.search-pattern.one.$(EXT).out: KRUN_OPTS += --search-one-step $(PATTERN_OPTS)
%.search-pattern.one.$(EXT).out: %.search-pattern.one.$(EXT) $(TEST_DEPS)
	$(KRUN) $(KRUN_OPTS) \
		--search-one-step --pattern "$$(cat $*.search-pattern.k)" \
		$< --output-file $@
	$(DIFF) $@.golden $@

%.search-pattern.plus.$(EXT).out: \
	KRUN_OPTS += --search-one-or-more-steps $(PATTERN_OPTS)
%.search-pattern.plus.$(EXT).out: %.search-pattern.plus.$(EXT) $(TEST_DEPS)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@
	$(DIFF) $@.golden $@

### PROVE

%-spec.k.out: %-spec.k $(TEST_DEPS)
	$(KPROVE) $(KPROVE_OPTS) $< --output-file $@ || true
	$(DIFF) $@.golden $@

%-spec.repl.k.out: %-spec.k $(TEST_DEPS)
	$(KPROVE) $(KPROVE_REPL_OPTS) $< --output-file $@ || true
	$(DIFF) $@.golden $@

%-spec.repl-script.k.out: \
	KPROVE_REPL_OPTS = \
		--haskell-backend-command \
		"$(KORE_REPL) -r --repl-script $<.repl"
%-spec.repl-script.k.out: %-spec.k $(TEST_DEPS)
	$(KPROVE) $(KPROVE_REPL_OPTS) \
		$< --output-file $@ \
		|| true
	$(DIFF) $@.golden $@

### BMC

%-spec.bmc.out: KPROVE_OPTS += --debug --raw-spec
%-spec.bmc.out: %-spec.bmc.k $(TEST_DEPS)
	$(KBMC) $(KPROVE_OPTS) --depth $(KBMC_DEPTH) $< --output-file $@ || true
	$(DIFF) $@.golden $@

### TARGETS

test: test-k

test-k: $(OUTS)

golden: $(foreach OUT, $(OUTS), $(OUT).golden)

clean:
	rm -fr $(KOMPILED) $(TEST_DIR)/*.out

.PHONY: test-k test golden clean
