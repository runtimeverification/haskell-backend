# Settings

TOP = $(shell git rev-parse --show-toplevel)
UPSTREAM_BRANCH = origin/master

BUILD_DIR = $(TOP)/.build
K_NIGHTLY = $(BUILD_DIR)/nightly.tar.gz
K_DIST = $(BUILD_DIR)/k
K_DIST_BIN = $(K_DIST)/bin
K_DIST_LIB = $(K_DIST)/lib
K_REPO = 'https://github.com/kframework/k'

# The kernel JAR is used as a build timestamp.
K = $(K_DIST_LIB)/java/kernel-1.0-SNAPSHOT.jar
KOMPILE = $(K_DIST_BIN)/kompile
KRUN = $(K_DIST_BIN)/krun
KPROVE = $(K_DIST_BIN)/kprove

HS_TOP = $(TOP)/src/main/haskell/kore
HS_SOURCE_DIRS = $(HS_TOP)/src $(HS_TOP)/app $(HS_TOP)/test $(HS_TOP)/bench
STACK_OPTS = --pedantic
STACK_BUILD_OPTS = $(STACK_OPTS) --no-run-tests --no-run-benchmarks
STACK_HADDOCK_OPTS = $(STACK_OPTS) --no-run-tests --no-run-benchmarks
STACK_TEST_OPTS = $(STACK_OPTS) --no-run-benchmarks
STACK_NO_PROFILE = --no-library-profiling --no-executable-profiling
STACK_FAST = --fast

STACK = stack
STACK_HADDOCK = $(STACK) --work-dir=.stack-work-haddock

# These paths are assigned with ?= so they will only be assigned once.
# Sub-processes will inherit the setting from their parent process.
STACK_LOCAL_INSTALL_ROOT ?= $(shell $(STACK) path --local-install-root)
STACK_LOCAL_DOC_ROOT ?= $(shell $(STACK_HADDOCK) path --local-doc-root)
STACK_LOCAL_HPC_ROOT ?= $(shell $(STACK_TEST) path --local-hpc-root)

ifdef BUILD_NUMBER
STACK_TEST_OPTS += --ta --xml=test-results.xml --coverage
endif

KORE_EXEC = $(STACK_LOCAL_INSTALL_ROOT)/bin/kore-exec
KORE_EXEC_OPTS =

$(KORE_EXEC):
	$(STACK) build --pedantic kore:exe:kore-exec

KOMPILE_OPTS = --backend haskell
KRUN_OPTS = --haskell-backend-command "$(KORE_EXEC) $(KORE_EXEC_OPTS)"
KPROVE_OPTS = --haskell-backend-command "$(KORE_EXEC) $(KORE_EXEC_OPTS)"
