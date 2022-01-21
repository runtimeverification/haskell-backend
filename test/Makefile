TARGETS = clean test test-simplifierx golden

SUBMAKES = $(shell find . -mindepth 2 -name Makefile)

$(TARGETS): $(SUBMAKES:=.make)

%/Makefile.make:
	$(MAKE) -C $* $(MAKECMDGOALS)

.PHONY: $(TARGETS)
