# Settings

TOP ?= $(shell git rev-parse --show-toplevel)

BUILD_DIR := $(TOP)/.build
K_SUBMODULE := $(BUILD_DIR)/k
K_BIN := $(K_SUBMODULE)/k-distribution/target/release/k/bin
KOMPILE := $(K_BIN)/kompile
KRUN := $(K_BIN)/krun

STACK_OPTS ?= --pedantic
STACK_BUILD_OPTS = $(STACK_OPTS) --no-run-tests --no-run-benchmarks
STACK_HADDOCK_OPTS = $(STACK_OPTS) --no-run-tests --no-run-benchmarks
STACK_TEST_OPTS = $(STACK_OPTS) --no-run-benchmarks

ifdef BUILD_NUMBER
STACK_TEST_OPTS += --ta --xml=test-results.xml
endif

STACK_LOCAL_INSTALL_ROOT != stack path --local-install-root
KORE_EXEC ?= $(STACK_LOCAL_INSTALL_ROOT)/bin/kore-exec
KORE_EXEC_OPTS ?=

KOMPILE_OPTS ?= --backend haskell
KRUN_OPTS ?= --haskell-backend-command "$(KORE_EXEC) $(KORE_EXEC_OPTS)"

KOMPILE_TARGETS := $(KOMPILE)
KRUN_TARGETS := $(KRUN) $(KORE_EXEC)

# Targets

FORCE:

$(K_SUBMODULE): FORCE
	if [ ! -d $(K_SUBMODULE) ]; then git submodule update --init -- $(K_SUBMODULE); fi
	cd $(K_SUBMODULE) && touch -d $$(git log --format=format:%cd -n 1) .

$(KORE_EXEC): FORCE
	stack build $(STACK_BUILD_OPTS) kore:exe:kore-exec

$(KOMPILE): $(K_SUBMODULE)
	cd $(K_SUBMODULE) && mvn package -q -DskipTests -U

$(KRUN): $(K_SUBMODULE)
	cd $(K_SUBMODULE) && mvn package -q -DskipTests -U
