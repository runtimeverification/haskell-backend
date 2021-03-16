# Settings

# Disable builtin rules to prevent obscure errors, such as:
# copying `test.sh` to `test.sh.out` if prerequisites are missing.
.SUFFIXES:
MAKEFLAGS += --no-builtin-rules

TOP ?= $(shell git rev-parse --show-toplevel)
export TOP  # so that sub-makes do not invoke git again

UPSTREAM_BRANCH = origin/master

BUILD_DIR = $(TOP)/.build

# The kernel JAR is used as a build timestamp.
KOMPILE = kompile
KRUN = krun
export KRUN
KPROVE = kprove
KBMC = kbmc

KOMPILE_OPTS = --backend haskell
KRUN_OPTS = --haskell-backend-command $(KORE_EXEC)
export KRUN_OPTS
KPROVE_OPTS = --haskell-backend-command $(KORE_EXEC)
export KPROVE_OPTS
KPROVE_REPL_OPTS = --haskell-backend-command $(KORE_REPL)
export KPROVE_REPL_OPTS

STACK_BUILD = build --pedantic $(STACK_BUILD_OPTS)

STACK = stack --allow-different-user
STACK_HADDOCK = $(STACK) --work-dir=.stack-work-haddock
STACK_TEST = $(STACK) --work-dir=.stack-work-test

KORE_PARSER = $(BUILD_DIR)/kore/bin/kore-parser
KORE_PARSER_OPTS =
export KORE_PARSER
export KORE_PARSER_OPTS

KORE_EXEC = $(BUILD_DIR)/kore/bin/kore-exec
KORE_EXEC_OPTS = --no-bug-report
export KORE_EXEC
export KORE_EXEC_OPTS

KORE_REPL = $(BUILD_DIR)/kore/bin/kore-repl
KORE_REPL_OPTS = --no-bug-report
export KORE_REPL
export KORE_REPL_OPTS

$(KORE_EXEC):
	$(STACK) $(STACK_BUILD) $(STACK_NO_PROFILE) --copy-bins kore:exe:kore-exec

$(KORE_REPL):
	$(STACK) $(STACK_BUILD) $(STACK_NO_PROFILE) --copy-bins kore:exe:kore-repl

$(KORE_PARSER):
	$(STACK) $(STACK_BUILD) $(STACK_NO_PROFILE) --copy-bins kore:exe:kore-parser
