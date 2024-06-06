DEF_KORE =

include $(CURDIR)/../include.mk

.PHONY: test

test: test.k
	@if $(KOMPILE) $(KOMPILE_OPTS) $< 2>&1 | grep 'Unsupported LHS of equation' > /dev/null;\
	  then echo "PASSED"; exit 0;\
	  else echo "FAILED"; exit 1;\
	fi
