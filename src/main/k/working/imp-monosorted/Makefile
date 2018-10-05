KORE_EXEC?="stack exec kore-exec --"
KOMPILE?=$(K_BIN)kompile
KRUN?=$(K_BIN)krun --haskell-backend-command $(KORE_EXEC)

imp-kompiled/definition.kore: imp.k
	$(KOMPILE) imp.k --backend haskell --syntax-module IMP

%.imp.kore: %.imp imp-kompiled/definition.kore
	$(KRUN) $< --dry-run

%.output: %.imp imp-kompiled/definition.kore
	$(KRUN) $< --output-file $@

%.krun: %.imp imp-kompiled/definition.kore
	$(KRUN) $<

%.test: %.output
	diff $< $<.golden

%.output.golden: %.output
	mv $< $<.golden

test: tests/sum.test tests/primes.test tests/collatz.test

k-test: tests/sum.test

golden: tests/sum.output.golden tests/primes.output.golden tests/collatz.output.golden

clean:
	rm -rf imp-kompiled tests/*.imp.kore tests/*.output

.PHONY: k-test test golden clean %.test %.krun