TOPTARGETS := all clean test test-k golden

.PHONY: $(TOPTARGETS)

SUBMAKES := $(shell find ./ ! -path ./Makefile -name Makefile)

# The subdirectory targets should not run in parallel, due to issues with
# running multiple concurrent krun processes.
.NOTPARALLEL:  $(SUBMAKES:=.make)
$(TOPTARGETS): $(SUBMAKES:=.make)

%/Makefile.make:
	$(MAKE) --directory $* $(MAKECMDGOALS)
