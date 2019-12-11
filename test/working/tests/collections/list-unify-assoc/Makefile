DEFINITION_NAME := list-unify-assoc

include $(CURDIR)/../../../include.mk

test: test-k

test-k: proofs/push-spec.kprove

clean:
	rm -rf $(KOMPILED)

.PHONY: test-k test clean %.kprove
