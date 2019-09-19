include include.mk

.PHONY: all clean docs haddock jenkins k-frontend \
        test test-kore test-k \
        kore-exec kore-repl

kore: kore-exec kore-repl

kore-exec: $(KORE_EXEC)

kore-repl: $(KORE_REPL)

k-frontend:
	mkdir -p $(BUILD_DIR)
	rm -rf $(K_DIST_DEFAULT) $(K_NIGHTLY)
	curl --location --output $(K_NIGHTLY) $(K_NIGHTLY_URL)
	mkdir -p $(K_DIST_DEFAULT)
	tar --extract --file $(K_NIGHTLY) --strip-components 1 --directory $(K_DIST_DEFAULT)
	cp src/main/kore/prelude.kore $(K_DIST_DEFAULT)/include/kore
	$(KRUN) --version

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

all: kore k-frontend

test: test-kore test-k

test-kore:
	$(STACK_TEST) $(STACK_BUILD) \
		--coverage \
		--test --bench --no-run-benchmarks \
		--ta --xml=test-results.xml

coverage_report: test-kore
	cp -r $$($(STACK_TEST) path --local-hpc-root) coverage_report

test-k:
	$(MAKE) --directory src/main/k/working test-k

test-bmc:
	$(MAKE) --directory src/main/k/in-progress/bmc/example1 test-bmc

clean:
	$(STACK) clean --full
	$(STACK_HADDOCK) clean --full
	$(STACK_TEST) clean --full
	find . -name '*.tix' -exec rm -f '{}' \;
	rm -f kore/test-results.xml
	rm -rf haskell_documentation
	rm -rf coverage_report
	rm -rf $(BUILD_DIR)
	$(MAKE) --directory src/main/k/working clean
