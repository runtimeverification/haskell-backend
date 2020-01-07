DEFINITION_NAME := kreflection

include $(CURDIR)/../../include.mk

test: tests/1.test-error

test-k: tests/1.test-error

%.test-error: %.output-error
	diff -u $<.golden $<

%.output-error: %.$(DEFINITION_NAME) $(DEFINITION) $(KORE_EXEC)
	$(KRUN) $(KRUN_OPTS) $< --output-file $@ 2>$@ || true

golden: tests/1.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun