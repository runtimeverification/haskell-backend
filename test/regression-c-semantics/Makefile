include $(CURDIR)/../include.mk

definition.kore: definition.kore.gz
	zcat $< >$@

test-regression-c-semantics.sh.out: definition.kore executable.kore
test-regression-c-semantics.sh.out: IGNORE_EXIT = false
