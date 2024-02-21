DEF = simplification
include $(CURDIR)/../include.mk

.PHONY: a-spec.k.out

a-spec.k.out: KORE_EXEC_OPTS = --debug-attempt-equation=SIMPLIFICATION.f.positive

a-spec.k.out: a-spec.k simplification.k $(TEST_DEPS)
	@echo ">>>" $(CURDIR) "kprove" $<
	rm -f $@
	$(KPROVE) $(KPROVE_OPTS) $(KPROVE_SPEC) 1> /dev/null 2> $@ || true
	grep -q "equation is not applicable" $@ && rm $@ || mv $@ $@.fail
