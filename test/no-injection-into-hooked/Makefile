ifeq ($(origin TOP), undefined)
	TOP = $(shell git rev-parse --show-toplevel)
endif

include $(TOP)/include.mk

KOMPILED = test-kompiled

test: test-k

test-k: test-kompiled/definition.kore

golden:

clean:
	rm -fr $(KOMPILED)

.PHONY: test-k test golden clean

test-kompiled/definition.kore: test.k $(K)
	@echo ">>>" $(CURDIR) "kompile" $<
	rm -fr $(KOMPILED)
	$(KOMPILE) $(KOMPILE_OPTS) $<; if [ $$? -eq 0 ]; then exit 1; fi
