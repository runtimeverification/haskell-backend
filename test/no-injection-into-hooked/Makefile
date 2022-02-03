ifeq ($(origin TOP), undefined)
	TOP = $(shell git rev-parse --show-toplevel)
endif

include $(TOP)/include.mk

KOMPILED = test-kompiled

test: test-k

build-test: $(TEST_DEPS)

test-simplifierx: test-k-simplifierx

test-k-simplifierx: KORE_EXEC_OPTS += --simplifierx
test-k-simplifierx: KORE_REPL_OPTS += --simplifierx
test-k-simplifierx: KORE_MATCH_DISJUNCTION_OPTS += --simplifierx
test-k-simplifierx: KORE_CHECK_FUNCTIONS_OPTS += --simplifierx
test-k-simplifierx: $(OUTS)

test-k: test-kompiled/definition.kore

golden:

clean:
	rm -fr $(KOMPILED)

clean-execution:

.PHONY: test-k test golden clean

test-kompiled/definition.kore: test.k $(K)
	@echo ">>>" $(CURDIR) "kompile" $<
	rm -fr $(KOMPILED)
	$(KOMPILE) $(KOMPILE_OPTS) $<; if [ $$? -eq 0 ]; then exit 1; fi
