# in nix, do not use the default binary location
ifneq ($(strip $(NIX)),)
export SERVER = kore-rpc
endif

test:
	python3 runTests.py

test-k: ;

clean: ;

build-test: ;

.PHONY: test test-k clean build-test
