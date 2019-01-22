include include.mk

.PHONY: all clean docs haddock jenkins kore k-frontend \
        test test-kore test-k

kore:
	stack build $(STACK_BUILD_OPTS)

kore-exec: $(KORE_EXEC)

k-frontend:
	mkdir -p $(BUILD_DIR)
	rm -rf $(K_DIST) $(K_NIGHTLY)
	curl --location --output $(K_NIGHTLY) \
	    $$(curl 'https://api.github.com/repos/kframework/k/releases' | jq --raw-output '.[0].assets[0].browser_download_url')
	mkdir --parents $(K_DIST)
	tar --extract --file $(K_NIGHTLY) --strip-components 1 --directory $(K_DIST)
	$(KRUN) --version

docs: haddock

$(STACK_LOCAL_DOC_ROOT)/index.html: STACK := $(STACK_HADDOCK)
$(STACK_LOCAL_DOC_ROOT)/index.html:
	$(STACK) haddock $(STACK_NO_PROFILE) $(STACK_FAST) --no-haddock-deps 2>&1 | tee haddock.log
	if grep -B 2 'Module header' haddock.log; then \
		echo >&2 "Please fix the missing documentation!"; \
		exit 1; \
	else \
		rm haddock.log; \
	fi

haddock: $(STACK_LOCAL_DOC_ROOT)/index.html

haskell_documentation: $(STACK_LOCAL_DOC_ROOT)/index.html
	cp -r $(STACK_LOCAL_DOC_ROOT) haskell_documentation

all: kore k-frontend

test: test-kore test-k

test-kore: $(STACK_LOCAL_HPC_ROOT)

$(STACK_LOCAL_HPC_ROOT): STACK := $(STACK_TEST)
$(STACK_LOCAL_HPC_ROOT):
	$(STACK) build \
		$(STACK_NO_PROFILE) $(STACK_FAST) $(STACK_COVERAGE) \
		--test --bench --no-run-benchmarks \
		--ta --xml=test-results.xml

coverage_report: $(STACK_LOCAL_HPC_ROOT)
	cp -r $(STACK_LOCAL_HPC_ROOT) coverage_report

test-k:
	$(MAKE) --directory src/main/k/working test-k

jenkins:
	$(MAKE) clean
	$(MAKE) check
	$(MAKE) all
	$(MAKE) test
	$(MAKE) docs

clean:
	$(STACK) clean --full
	$(STACK_HADDOCK) clean --full
	$(STACK_TEST) clean --full
	find . -name '*.tix' -exec rm -f '{}' \;
	rm -f src/main/haskell/kore/test-results.xml
	rm -rf haskell_documentation
	rm -rf coverage_report
	rm -rf $(BUILD_DIR)
	$(MAKE) --directory src/main/k/working clean

check:
	if ! ./scripts/git-assert-clean.sh; \
	then \
		echo >&2 "Please commit your changes!"; \
		exit 1; \
	fi
	if ! ./scripts/git-rebased-on.sh "$$(git rev-parse $(UPSTREAM_BRANCH))" --linear; \
	then \
		echo >&2 "Please rebase your branch onto ‘master’!"; \
		exit 1; \
	fi
	$(TOP)/scripts/stylish.sh
	if ! ./scripts/git-assert-clean.sh; \
	then \
		echo >&2 "Please run ‘scripts/stylish.sh’ to fix style errors!"; \
		exit 1; \
	fi
