ifeq ($(origin TOP), undefined)
	TOP = $(shell git rev-parse --show-toplevel)
endif

DEF_KORE =
include $(TOP)/include.mk

DIFF = diff -u
%.golden: DIFF = true

FAILED = ( mv $@ $@.fail && false )

TESTS = $(wildcard *.kore)
OUTS += $(foreach TEST, $(TESTS), $(TEST).out)
GOLDEN += $(foreach TEST, $(TESTS), $(TEST).golden)

%.kore.out : %.kore
	$(KORE_PARSER) --no-print-definition $< 2>$@ || true
	$(DIFF) $*.kore.golden $@ || $(FAILED)

%.golden: %.out
	cp $< $@

### TARGETS

test: test-k

test-simplifierx: test-k-simplifierx

test-k-simplifierx: KORE_EXEC_OPTS += --simplifierx
test-k-simplifierx: KORE_REPL_OPTS += --simplifierx
test-k-simplifierx: KORE_MATCH_DISJUNCTION_OPTS += --simplifierx
test-k-simplifierx: KORE_CHECK_FUNCTIONS_OPTS += --simplifierx
test-k-simplifierx: $(OUTS)

test-k: $(OUTS)

build-test:

golden: $(GOLDEN)

clean: clean-execution

clean-execution:
	rm -fr *.out *.fail

.PHONY: test-k test golden clean
