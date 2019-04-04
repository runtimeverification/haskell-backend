DEFINITION_NAME := smt-lemma

include $(CURDIR)/../../include.mk

test: tests/1.smt-lemma tests/2.smt-lemma tests/3.smt-lemma

test-prove: prove/one-spec.kprove

test-k: tests/1.smt-lemma tests/2.smt-lemma tests/3.smt-lemma \
    	test-prove

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden tests/4.output.golden

clean:
	rm -rf $(KOMPILED) tests/*.output

.PHONY: test-k test golden clean %.test %.krun test-prove
