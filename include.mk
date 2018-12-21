# Settings

TOP ?= $(shell git rev-parse --show-toplevel)
UPSTREAM_BRANCH := origin/master
NPROCS := 4

BUILD_DIR := $(TOP)/.build
K_NIGHTLY := $(BUILD_DIR)/nightly.tar.gz
K_DIR := $(BUILD_DIR)/k
# The K submodule reflog is used as a source timestamp.
K_BIN := $(K_DIR)/bin
K_LIB := $(K_DIR)/lib
K_REPO := 'https://github.com/kframework/k'

# The kernel JAR is used as a build timestamp.
K := $(K_LIB)/java/kernel-1.0-SNAPSHOT.jar
JAVA_CLASSPATH := '$(K_LIB)/java/*'
JAVA := java -ea -cp $(JAVA_CLASSPATH)
KOMPILE := $(K_BIN)/kompile
KRUN := $(K_BIN)/krun
KPROVE := $(K_BIN)/kprove

HS_TOP := $(TOP)/src/main/haskell/kore
HS_SOURCE_DIRS := $(HS_TOP)/src $(HS_TOP)/app $(HS_TOP)/test $(HS_TOP)/bench
STACK_OPTS ?= --pedantic
STACK_BUILD_OPTS = $(STACK_OPTS) --no-run-tests --no-run-benchmarks
STACK_HADDOCK_OPTS = $(STACK_OPTS) --no-run-tests --no-run-benchmarks
STACK_TEST_OPTS = $(STACK_OPTS) --no-run-benchmarks

ifdef BUILD_NUMBER
STACK_TEST_OPTS += --ta --xml=test-results.xml
endif

STACK_LOCAL_INSTALL_ROOT := $(shell stack path --local-install-root)
KORE_EXEC ?= $(STACK_LOCAL_INSTALL_ROOT)/bin/kore-exec
KORE_EXEC_OPTS ?=

KOMPILE_OPTS ?= --backend haskell
KRUN_OPTS ?= --haskell-backend-command "$(KORE_EXEC) $(KORE_EXEC_OPTS)"
KPROVE_OPTS ?= --haskell-backend-command "$(KORE_EXEC) $(KORE_EXEC_OPTS)"

# Targets

FORCE:

$(KORE_EXEC): FORCE
	stack build $(STACK_BUILD_OPTS) kore:exe:kore-exec
