DEFINITION_NAME := run
MODULE_NAME := RUN

include $(CURDIR)/../include.mk

all_tests := a b

test: $(foreach test, $(all_tests), $(test).test)

test-k: test

golden: $(foreach test, $(all_tests), $(test).output.golden)

clean:
	rm -rf $(KOMPILED) *.output

.PHONY: test-k test golden clean %.test
