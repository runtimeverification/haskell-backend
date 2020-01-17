DEF = kreflection

include $(CURDIR)/../include.mk

# Disable default test
1.kreflection.out:
	true

test-kreflection.sh.out: $(DEF_KORE)
test-kreflection.sh.out: KORE_EXEC_OPTS += --disable-log-timestamps
