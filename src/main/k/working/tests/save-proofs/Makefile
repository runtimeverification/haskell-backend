DEFINITION_NAME := save-proofs

include $(CURDIR)/../../include.mk

test-save-chain: save-proofs/test.save-chain

test-k: test-save-chain

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun test-save-chain
