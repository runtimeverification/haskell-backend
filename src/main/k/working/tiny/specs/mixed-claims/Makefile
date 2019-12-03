DEFINITION_NAME := ../../tiny

include $(CURDIR)/../../../include.mk

SPEC_FILE := mixed-claims-spec.k

repl-test: scripts/automatic.repl.test scripts/manual.repl.test

repl-golden: scripts/automatic.repl.output.golden scripts/manual.repl.output.golden

test-k: repl-test
