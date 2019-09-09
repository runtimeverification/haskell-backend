# Settings

TOP ?= $(shell git rev-parse --show-toplevel)
export TOP  # so that sub-makes do not invoke git again
UPSTREAM_BRANCH = origin/master

BUILD_DIR = $(TOP)/.build
K_NIGHTLY = $(BUILD_DIR)/nightly.tar.gz
K_NIGHTLY_URL = $(shell cat deps/k_release)/nightly.tar.gz
K_DIST_DEFAULT = $(BUILD_DIR)/k
K_DIST ?= $(K_DIST_DEFAULT)
K_DIST_BIN = $(K_DIST)/bin
K_DIST_LIB = $(K_DIST)/lib

# The kernel JAR is used as a build timestamp.
K = $(K_DIST_LIB)/java/kernel-1.0-SNAPSHOT.jar
KOMPILE = $(K_DIST_BIN)/kompile
KRUN = $(K_DIST_BIN)/krun
KPROVE = $(K_DIST_BIN)/kprove
KBMC = $(K_DIST_BIN)/kbmc

KOMPILE_OPTS = --backend haskell
KRUN_OPTS = --haskell-backend-command "$(KORE_EXEC) $(KORE_EXEC_OPTS)"
KPROVE_OPTS = --haskell-backend-command "$(KORE_EXEC) $(KORE_EXEC_OPTS)"
KPROVE_REPL_OPTS = --haskell-backend-command "$(KORE_REPL) $(KORE_EXEC_OPTS)"

HS_TOP = $(TOP)/kore
HS_SOURCE_DIRS = $(HS_TOP)/src $(HS_TOP)/app $(HS_TOP)/test $(HS_TOP)/bench
STACK_BUILD = build --pedantic $(STACK_BUILD_OPTS)

STACK = stack
STACK_HADDOCK = $(STACK) --work-dir=.stack-work-haddock
STACK_TEST = $(STACK) --work-dir=.stack-work-test

KORE_EXEC = $(BUILD_DIR)/kore/bin/kore-exec
KORE_EXEC_OPTS =

KORE_REPL = $(BUILD_DIR)/kore/bin/kore-repl

$(KORE_EXEC):
	$(STACK) $(STACK_BUILD) $(STACK_NO_PROFILE) --copy-bins kore:exe:kore-exec

$(KORE_REPL):
	$(STACK) $(STACK_BUILD) $(STACK_NO_PROFILE) --copy-bins kore:exe:kore-repl
