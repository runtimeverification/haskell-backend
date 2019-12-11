ifeq ($(origin TOP), undefined)
	TOP = $(shell git rev-parse --show-toplevel)
endif

include $(TOP)/include.mk

DEFINITION_NAME := test-k-equal
KOMPILED := $(DEFINITION_NAME)-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION) : $(DEFINITION_NAME).k
	$(KOMPILE) $(KOMPILE_OPTS) $<

specs := \
	iszero-eq-spec \
	iszero-ge-spec \
	iszero-gt-spec

all_tests := $(specs)

%.kprove: %.k $(DEFINITION) $(KORE_EXEC)
	$(KPROVE) $(KPROVE_OPTS) -d . -m VERIFICATION $< --output-file $@ || exit 0

%.kprove.golden: %.kprove
	mv $< $@

%.test-spec: %.kprove
	diff -u $<.golden $<
	rm $<

.PHONY: test test-k test-prove golden clean %.test-spec

test: test-prove

test-k: test-prove

test-prove: $(foreach spec, $(specs), specs/$(spec).test-spec)

golden: $(foreach spec, $(specs), specs/$(spec).kprove.golden)

clean:
	rm -rf $(KOMPILED) specs/*.output tests/*.output
