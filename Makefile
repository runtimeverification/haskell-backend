include include.mk

jenkins: STACK_OPTS += --test --bench --coverage
export STACK_OPTS

.PHONY: all clean clean-submodules distclean docs haddock jenkins kore stylish \
        test test-kore test-k

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

jenkins: distclean check all test docs

distclean: clean
	if test -f $(K_SUBMODULE)/pom.xml; then \
		cd $(K_SUBMODULE) && mvn clean -q; \
	fi
	git submodule deinit --force -- ./

clean: clean-submodules
	stack clean
	find -name '*.tix' -exec rm -f '{}' \;
	$(MAKE) -C src/main/k/working clean

check:
	if ! ./scripts/git-assert-clean.sh; \
	then \
		echo >&2 "Please commit your changes!"; \
		exit 1; \
	fi
	if ! ./scripts/git-rebased-on.sh "$$(git rev-parse origin/master)" --linear; \
	then \
		echo >&2 "Please rebase your branch onto ‘master’!"; \
		exit 1; \
	fi
	$(MAKE) stylish
	if ! ./scripts/git-assert-clean.sh; \
	then \
		echo >&2 "Please run ‘make stylish’ to fix style errors!"; \
		exit 1; \
	fi

stylish:
	if ! command -v stylish-haskell; then\
		stack install stylish-haskell; \
	fi
	find $(HS_SOURCE_DIRS) \
		\( -name '*.hs' -o -name '*.hs-boot' \) \
		-exec stylish-haskell -i '{}' \;
