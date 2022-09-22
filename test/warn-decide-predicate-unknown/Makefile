DEF = verification
MODULE := VERIFICATION
include $(CURDIR)/../include.mk
KORE_EXEC_OPTS += --smt none

lemmas-no-smt-spec.k.out: lemmas-no-smt-spec.k lemmas.k verification.k $(TEST_DEPS)
	@echo ">>>" $(CURDIR) "kprove" $<
	@echo "KORE_EXEC_OPTS =" $(KORE_EXEC_OPTS)
	rm -f $@
	$(if $(STORE_PROOFS),rm -f $(STORE_PROOFS),$(if $(RECALL_PROOFS),cp $(RECALL_PROOFS) $(@:.out=.save-proofs.kore)))
	$(KPROVE) $(KPROVE_OPTS) $(KPROVE_SPEC_OPTS) $(KPROVE_SPEC) 2>&1 1>/dev/null | grep -q "Warning (DecidePredicateUnknown)"