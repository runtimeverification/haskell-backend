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

max-inconsistent-prelude-spec.k.out: \
    KPROVE_OPTS += --spec-module MAX-SPEC
max-inconsistent-prelude-spec.k.out: \
	KORE_EXEC_OPTS += --smt-prelude inconsistent-prelude.smt2
max-inconsistent-prelude-spec.k.out: max-inconsistent-prelude-spec.k imp.k $(TEST_DEPS)
	@echo ">>>" $(CURDIR) "kprove" $<
	rm -f $@
	$(KPROVE) $(KPROVE_OPTS) $(KPROVE_SPEC) 1> /dev/null 2> $@ || true
	grep -q "The definitions sent to the solver are inconsistent." $@ || mv $@ $@.fail

max-consistent-prelude-spec.k.out: \
    KPROVE_OPTS += --spec-module MAX-SPEC
max-consistent-prelude-spec.k.out: \
	KORE_EXEC_OPTS += --smt-prelude consistent-prelude.smt2
