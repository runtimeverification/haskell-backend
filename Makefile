# Settings
# --------

BUILD_DIR:=$(CURDIR)/.build
K_SUBMODULE:=$(BUILD_DIR)/k
export K_BIN=$(K_SUBMODULE)/k-distribution/target/release/k/bin/

.PHONY: all clean deps k-deps distclean clean-submodules kore-exec

all: kore-exec

test: kore-test k-test

kore-test:
	stack test --pedantic

k-test: kore-exec k-deps
	$(MAKE) -C src/main/k/working k-test

kore-exec:
	stack build kore:exe:kore-exec

deps: k-deps

distclean: clean
	cd $(K_SUBMODULE) \
		&& mvn clean -q
	git submodule deinit --force -- ./

clean: clean-submodules
	stack clean
	$(MAKE) -C src/main/k/working clean
	rm -rf $(BUILD_DIR)/bin

clean-submodules:
	rm -rf $(K_SUBMODULE)/make.timestamp


k-deps: $(K_SUBMODULE)/make.timestamp

$(K_SUBMODULE)/make.timestamp:
	@echo "== submodule: $@"
	git submodule update --init -- $(K_SUBMODULE)
	cd $(K_SUBMODULE) \
		&& mvn package -q -DskipTests -U
	touch $(K_SUBMODULE)/make.timestamp

