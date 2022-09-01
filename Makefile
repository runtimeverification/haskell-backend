include include.mk

.PHONY: all kore clean clean-execution docs haddock \
		test test-kore test-k test-k-simplifierx test-simplifierx \
		kore-exec kore-repl kore-parser kore-check-functions \
		kore-format kore-match-disjunction kore-prof

all: kore-exec kore-repl kore-parser kore-check-functions kore-format \
	kore-match-disjunction kore-prof

kore: all

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
        #remove header warning for Paths_kore
	sed -e "/.*in 'Paths_kore'$/{n;n;/^ *Module header$/d}" haddock.log | tee haddock.log.noPaths
	if grep -B 2 'Module header' haddock.log.noPaths; then \
		echo >&2 "Please fix the missing documentation!"; \
		exit 1; \
	else \
		rm haddock.log*; \
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

build-test:
	$(MAKE) -C test build-test

test-k:
	$(MAKE) -C test test

test-k-simplifierx:
	$(MAKE) -C test test-simplifierx

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

clean-execution:
	$(MAKE) -C test clean-execution

.PHONY: hoogle-cert hoogle-server
HOOGLE_WORKDIR = .stack-work-haddock/hoogle
HOOGLE        ?= $(shell which hoogle)
HOOGLE_DB     := $(HOOGLE_WORKDIR)/*/*/*/database.hoo


hoogle-data: $(HOOGLE_DB)

$(HOOGLE_DB): # could depend on source code but would slow things down
	$(STACK_HADDOCK) hoogle --setup

hoogle-clean:
	rm -rf $(HOOGLE_WORKDIR)

hoogle-refresh: hoogle-clean hoogle-data

define check_hoogle
	@if ${HOOGLE} --version; then return 0; else echo "Hoogle not installed"; exit 1; fi
endef


hoogle: hoogle-data
	$(call check_hoogle)
	@read -p "Query:" QUERY && $(HOOGLE) --database $(HOOGLE_DB) "$$QUERY"

ifeq ($(HOOGLE_USE_SSL),yes)

SSL_OPTS=--https --cert=$(HOOGLE_WORKDIR)/hoogle.crt --key=$(HOOGLE_WORKDIR)/hoogle.key

hoogle-cert:
	@openssl req -newkey rsa:1024 -x509 -sha256 -days 1 -nodes -out $(HOOGLE_WORKDIR)/hoogle.crt -keyout $(HOOGLE_WORKDIR)/hoogle.key -subj "/C=US/ST=MI/O=RuntimeVerification/CN=*"

hoogle-server: hoogle-cert
endif

hoogle-server: hoogle-data
	$(call check_hoogle)
	@echo "Running hoogle server (press ^C to exit)"
	@$(HOOGLE) server \
		--database $(HOOGLE_DB) \
		--host=* \
		$(SSL_OPTS)
