DEF_KORE = $(KORE_FILES)

include $(CURDIR)/../include.mk

KORE_FILES=$(wildcard [a-z]*definition.kore)

test: $(addprefix test-,$(basename $(KORE_FILES)))

MODULE=UNDEFINED-MODULE

# lame solution: specify the --module $MODULE individually instead of grep|tail|sed
test-a-to-f-definition: MODULE=TEST
test-test-smoke-definition: MODULE=C
test-test-totalSupply-definition: MODULE=VERIFICATION

test-%: %.kore
	@echo "Serializing definition $<"
	time -f "%esec" $(KORE_EXEC) $< --output serialized.bin --module $(MODULE) --serialize
	@echo "Loading serialized definition (to hit an error afterwards)"
	time -f "%esec" sh -c "$(KORE_EXEC) serialized.bin \
		--module $(MODULE) \
		--pattern serialized.bin \
		--debug-rewrite FAIL-ME-PLEASE 2>&1 | \
		grep FAIL-ME-PLEASE"
	@rm serialized.bin

clean:

golden:
