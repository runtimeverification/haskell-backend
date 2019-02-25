include $(CURDIR)/../include.mk

KOMPILED := search-kompiled
DEFINITION := $(KOMPILED)/definition.kore

$(DEFINITION) : lem.k
	$(KOMPILE) $(KOMPILE_OPTS) $< --syntax-module LEM

%.output: %.lem $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@

%.krun: %.search $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $<

%.test: %.output
	diff -u $<.golden $<

%.output.golden: %.output
	mv $< $<.golden

test: test-k

test-k: \
	tests/pgm.test \

golden: \
	tests/pgm.output.golden \

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun
