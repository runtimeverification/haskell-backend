# Settings

# Disable builtin rules to prevent obscure errors, such as:
# copying `test.sh` to `test.sh.out` if prerequisites are missing.
.SUFFIXES:
MAKEFLAGS += --no-builtin-rules

TOP ?= $(shell git rev-parse --show-toplevel)
export TOP  # so that sub-makes do not invoke git again

UPSTREAM_BRANCH = origin/master

BUILD_DIR = $(TOP)/.build
K_RELEASE_TAR = $(BUILD_DIR)/k-nightly.tar.gz
K_RELEASE_TAR_URL = https://github.com/kframework/k/releases/download/$(shell cat $(TOP)/deps/k_release)/k-nightly.tar.gz
K_RELEASE_DEFAULT = $(BUILD_DIR)/k
K_RELEASE ?= $(K_RELEASE_DEFAULT)
K_RELEASE_BIN = $(K_RELEASE)/bin
K_RELEASE_LIB = $(K_RELEASE)/lib

# The kernel JAR is used as a build timestamp.
K = $(K_RELEASE_LIB)/kframework/java/kernel-1.0-SNAPSHOT.jar
KOMPILE = $(K_RELEASE_BIN)/kompile
KRUN = $(K_RELEASE_BIN)/krun
export KRUN
KPROVE = $(K_RELEASE_BIN)/kprove
KBMC = $(K_RELEASE_BIN)/kbmc

KOMPILE_OPTS = --backend haskell
KRUN_OPTS = --haskell-backend-command $(KORE_EXEC)
export KRUN_OPTS
KPROVE_OPTS = --haskell-backend-command $(KORE_EXEC)
export KPROVE_OPTS
KPROVE_REPL_OPTS = --haskell-backend-command $(KORE_REPL)
export KPROVE_REPL_OPTS

HS_TOP = $(TOP)/kore
HS_SOURCE_DIRS = $(HS_TOP)/src $(HS_TOP)/app $(HS_TOP)/test $(HS_TOP)/bench
STACK_BUILD = build --pedantic $(STACK_BUILD_OPTS)

STACK = stack --allow-different-user
STACK_HADDOCK = $(STACK) --work-dir=.stack-work-haddock
STACK_TEST = $(STACK) --work-dir=.stack-work-test

KORE_PARSER = $(BUILD_DIR)/kore/bin/kore-parser
KORE_PARSER_OPTS =
export KORE_PARSER
export KORE_PARSER_OPTS

KORE_EXEC = $(BUILD_DIR)/kore/bin/kore-exec
KORE_EXEC_OPTS =
export KORE_EXEC
export KORE_EXEC_OPTS

KORE_REPL = $(BUILD_DIR)/kore/bin/kore-repl
KORE_REPL_OPTS =
export KORE_REPL
export KORE_REPL_OPTS

$(KORE_EXEC):
	$(STACK) $(STACK_BUILD) $(STACK_NO_PROFILE) --copy-bins kore:exe:kore-exec

$(KORE_REPL):
	$(STACK) $(STACK_BUILD) $(STACK_NO_PROFILE) --copy-bins kore:exe:kore-repl

$(KORE_PARSER):
	$(STACK) $(STACK_BUILD) $(STACK_NO_PROFILE) --copy-bins kore:exe:kore-parser

$(K_RELEASE_DEFAULT)/lib/kframework/java/kernel-1.0-SNAPSHOT.jar:
	mkdir -p $(BUILD_DIR)
	rm -rf $(K_RELEASE_DEFAULT) $(K_RELEASE_TAR)
	curl --location --output $(K_RELEASE_TAR) $(K_RELEASE_TAR_URL)
	mkdir -p $(K_RELEASE_DEFAULT)
	tar --extract --file $(K_RELEASE_TAR) --strip-components 1 --directory $(K_RELEASE_DEFAULT)
	cp $(TOP)/src/main/kore/prelude.kore $(K_RELEASE_DEFAULT)/include/kore
	$(KRUN) --version
	test -f $@
