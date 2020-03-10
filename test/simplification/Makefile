DEF = simplification
include $(CURDIR)/../include.mk

KORE_EXEC_OPTS = --log-level=debug

a-spec.k.out: a-spec.k simplification.k $(TEST_DEPS)
	@echo ">>>" $(CURDIR) "kprove" $<
	rm -f $@
	$(KPROVE) $(KPROVE_OPTS) $(KPROVE_SPEC) 1> /dev/null 2> $@ || true
	grep -q "Skipping simplification rule due to pre-condition being unmet" $@