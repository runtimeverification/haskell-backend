include $(CURDIR)/../include.mk

definition.kore: definition.kore.gz
	zcat $< >$@

test-regression-c-semantics.sh.out: definition.kore executable.kore
