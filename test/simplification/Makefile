DEF = simplification
include $(CURDIR)/../include.mk

a-spec.k.out: a-spec.k simplification.k $(TEST_DEPS)
	@echo ">>>" $(CURDIR) "kprove" $<
	rm -f $@
	$(KPROVE) $(KPROVE_OPTS) $(KPROVE_SPEC) 1> /dev/null 2> $@ || true
	grep -q "Simplification result with remainder" $@