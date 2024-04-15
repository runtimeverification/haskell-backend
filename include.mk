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

KOMPILE_OPTS = --backend haskell --haskell-backend-command $(KORE_EXEC)
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

ifeq ($(strip $(NIX)),)
KORE_PARSER = $(BUILD_DIR)/kore/bin/kore-parser
else
KORE_PARSER = kore-parser
endif
KORE_PARSER_OPTS =
export KORE_PARSER
export KORE_PARSER_OPTS

ifeq ($(strip $(NIX)),)
KORE_EXEC = $(BUILD_DIR)/kore/bin/kore-exec
else
KORE_EXEC = kore-exec
endif
KORE_EXEC_OPTS = --no-bug-report
export KORE_EXEC
export KORE_EXEC_OPTS

ifeq ($(strip $(NIX)),)
KORE_REPL = $(BUILD_DIR)/kore/bin/kore-repl
else
KORE_REPL = kore-repl
endif
KORE_REPL_OPTS = --no-bug-report
export KORE_REPL
export KORE_REPL_OPTS

KORE_FORMAT = $(BUILD_DIR)/kore/bin/kore-format
KORE_FORMAT_OPTS = --no-bug-report
export KORE_FORMAT
export KORE_FORMAT_OPTS

KORE_MATCH_DISJUNCTION = $(BUILD_DIR)/kore/bin/kore-match-disjunction
KORE_MATCH_DISJUNCTION_OPTS = --no-bug-report
export KORE_MATCH_DISJUNCTION
export KORE_MATCH_DISJUNCTION_OPTS

$(BUILD_DIR)/kore/bin/kore-exec:
	$(STACK) $(STACK_BUILD) $(STACK_NO_PROFILE) --copy-bins kore:exe:kore-exec

$(BUILD_DIR)/kore/bin/kore-repl:
	$(STACK) $(STACK_BUILD) $(STACK_NO_PROFILE) --copy-bins kore:exe:kore-repl

$(BUILD_DIR)/kore/bin/kore-parser:
	$(STACK) $(STACK_BUILD) $(STACK_NO_PROFILE) --copy-bins kore:exe:kore-parser

$(BUILD_DIR)/kore/bin/kore-format:
	$(STACK) $(STACK_BUILD) $(STACK_NO_PROFILE) --copy-bins kore:exe:kore-format

$(BUILD_DIR)/kore/bin/kore-match-disjunction:
	$(STACK) $(STACK_BUILD) $(STACK_NO_PROFILE) --copy-bins kore:exe:kore-match-disjunction
