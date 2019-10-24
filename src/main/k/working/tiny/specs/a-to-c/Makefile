DEFINITION_NAME := ../../tiny

include $(CURDIR)/../../../include.mk

SPEC_FILE := a-to-c-spec.k

repl-test: scripts/automatic.repl.test scripts/manual.repl.test scripts/automatic-stepf.repl.test

repl-golden: scripts/automatic.repl.output.golden scripts/manual.repl.output.golden scripts/automatic-stepf.repl.output.golden

test-k: repl-test
