include include.mk

jenkins: STACK_OPTS += --test --bench --coverage
export STACK_OPTS

.PHONY: all docs haddock jenkins kore test test-kore test-k distclean clean clean-submodules

kore:
	stack build $(STACK_BUILD_OPTS)

docs: haddock

haddock:
	stack haddock --no-haddock-deps $(STACK_HADDOCK_OPTS)
	if [ -n "$$BUILD_NUMBER" ]; then \
		cp -r $$(stack path --local-doc-root) haskell_documentation; \
	fi

all: kore

test: test-kore test-k

test-kore:
	stack test $(STACK_TEST_OPTS)
	if [ -n "$$BUILD_NUMBER" ]; then \
		cp -r $$(stack path --local-hpc-root) coverage_report; \
	fi

test-k:
	$(MAKE) -C src/main/k/working test-k

jenkins: all test docs

distclean: clean
	cd $(K_SUBMODULE) \
		&& mvn clean -q
	git submodule deinit --force -- ./

clean: clean-submodules
	stack clean
	find -name '*.tix' -exec rm -f '{}' \;
	$(MAKE) -C src/main/k/working clean

check:
	./scripts/git-rebased-on.sh master --linear
