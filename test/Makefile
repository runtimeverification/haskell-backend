TARGETS = clean test golden

DIRS = in-progress working
SUBMAKES = $(foreach DIR,$(DIRS),$(DIR)/Makefile.make)

$(TARGETS): $(SUBMAKES)

%/Makefile.make:
	$(MAKE) -C $* $(MAKECMDGOALS)

.PHONY: $(TARGETS)
