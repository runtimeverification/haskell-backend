include ../../include.mk

TOPTARGETS := all clean test test-k golden

.PHONY: $(TOPTARGETS)

SUBDIRS := $(wildcard */.)

# The subdirectory targets should not run in parallel, due to issues with
# running multiple concurrent krun processes.
$(TOPTARGETS):
	for subdir in $(SUBDIRS); do \
		$(MAKE) -C "$$subdir" $(MAKECMDGOALS); \
	done
