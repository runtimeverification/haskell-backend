# Settings

TOP ?= $(shell git rev-parse --show-toplevel)

BUILD_DIR := $(TOP)/.build
K_SUBMODULE := $(BUILD_DIR)/k
# The K submodule reflog is used as a source timestamp.
K_SRC := $(TOP)/.git/modules/deps/k/logs/HEAD
K_PACKAGE := $(K_SUBMODULE)/k-distribution/target/release/k
K_BIN := $(K_PACKAGE)/bin
K_LIB := $(K_PACKAGE)/lib

# The kernel JAR is used as a build timestamp.
K := $(K_LIB)/java/kernel-1.0-SNAPSHOT.jar
JAVA_CLASSPATH := '$(K_LIB)/java/*'
JAVA := java -ea -cp $(JAVA_CLASSPATH)
KOMPILE := $(K_BIN)/kompile
KRUN := $(K_BIN)/krun

HS_TOP := $(TOP)/src/main/haskell/kore
HS_SOURCE_DIRS := $(HS_TOP)/src $(HS_TOP)/app $(HS_TOP)/test $(HS_TOP)/bench
STACK_OPTS ?= --pedantic
STACK_BUILD_OPTS = $(STACK_OPTS) --no-run-tests --no-run-benchmarks
STACK_HADDOCK_OPTS = $(STACK_OPTS) --no-run-tests --no-run-benchmarks
STACK_TEST_OPTS = $(STACK_OPTS) --no-run-benchmarks

ifdef BUILD_NUMBER
STACK_TEST_OPTS += --ta --xml=test-results.xml
endif

STACK_LOCAL_INSTALL_ROOT := $(shell stack path --local-install-root)
KORE_EXEC ?= $(STACK_LOCAL_INSTALL_ROOT)/bin/kore-exec
KORE_EXEC_OPTS ?=

KOMPILE_OPTS ?= --backend haskell
KRUN_OPTS ?= --haskell-backend-command "$(KORE_EXEC) $(KORE_EXEC_OPTS)"

# Targets

FORCE:

$(K_SUBMODULE): FORCE
	if test ! -f $(K_SUBMODULE)/pom.xml; then \
		git submodule update --init -- $(K_SUBMODULE); \
	fi

$(K_SRC): $(K_SUBMODULE)

$(KORE_EXEC): FORCE
	stack build $(STACK_BUILD_OPTS) kore:exe:kore-exec

$(K): $(K_SRC)
	cd $(K_SUBMODULE) && mvn package -q -DskipTests -U
	rm -f $(K_BIN)/ng
