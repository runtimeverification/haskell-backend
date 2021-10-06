include include.mk

.PHONY: all clean docs haddock \
		test test-kore test-k \
		kore-exec kore-repl kore-parser kore-check-functions \
		kore-format kore-match-disjunction kore-prof

all: kore-exec kore-repl kore-parser kore-check-functions kore-format \
	kore-match-disjunction kore-prof

kore-exec: $(KORE_EXEC)

kore-repl: $(KORE_REPL)

kore-parser: $(KORE_PARSER)

kore-check-functions: $(KORE_CHECK_FUNCTIONS)

kore-format: $(KORE_FORMAT)

kore-match-disjunction: $(KORE_MATCH_DISJUNCTION)

kore-prof: $(KORE_PROF)

docs: haddock

haddock:
	$(STACK_HADDOCK) haddock \
		--fast \
		>haddock.log 2>&1 \
		|| ( cat haddock.log; exit 1; )
	cat haddock.log
	if grep -B 2 'Module header' haddock.log; then \
		echo >&2 "Please fix the missing documentation!"; \
		exit 1; \
	else \
		rm haddock.log; \
	fi

haskell_documentation: haddock
	cp -r $$($(STACK_HADDOCK) path --local-doc-root) haskell_documentation

test: test-kore test-k

test-kore:
	$(STACK_TEST) $(STACK_BUILD) \
		--coverage --fast \
		--test --bench --no-run-benchmarks \
		--ta --xml=test-results.xml

coverage_report: test-kore
	cp -r $$($(STACK_TEST) path --local-hpc-root) coverage_report

test-k:
	$(MAKE) -C test test

clean:
	$(STACK) clean --full
	$(STACK_HADDOCK) clean --full
	$(STACK_TEST) clean --full
	find . -name '*.tix' -exec rm -f '{}' \;
	rm -f kore/test-results.xml
	rm -rf haskell_documentation
	rm -rf coverage_report
	rm -rf $(BUILD_DIR)
	$(MAKE) -C test clean
