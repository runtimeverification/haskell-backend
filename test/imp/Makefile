DEF = imp
KORE_MODULE = IMP
GOLDEN += sum-save-proofs-spec.k.save-proofs.kore.golden
include $(CURDIR)/../include.mk

run-stepf-repl-script-spec.k.out: \
    KPROVE_OPTS += --spec-module SUM-SPEC

max-breadth-limit-one-spec.k.out: \
    KPROVE_OPTS += --spec-module MAX-SPEC
max-breadth-limit-one-spec.k.out: \
	KORE_EXEC_OPTS += --breadth 1

sum-breadth-limit-three-spec.k.out: \
	KPROVE_OPTS += --spec-module SUM-SPEC
sum-breadth-limit-three-spec.k.out: \
	KORE_EXEC_OPTS += --breadth 3
