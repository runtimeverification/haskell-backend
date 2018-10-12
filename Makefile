include include.mk

.PHONY: all test test-kore test-k distclean clean clean-submodules

all: kore-exec

test: test-kore test-k

test-kore:
	$(STACK) test $(STACK_TEST_OPTS)

test-k:
	$(MAKE) -C src/main/k/working test-k

distclean: clean
	cd $(K_SUBMODULE) \
		&& mvn clean -q
	git submodule deinit --force -- ./

clean: clean-submodules
	stack clean
	$(MAKE) -C src/main/k/working clean

clean-submodules:
	rm -rf $(K_TIMESTAMP)
