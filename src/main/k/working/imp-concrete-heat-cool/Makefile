imp-kompiled/definition.kore: imp.k
	kompile imp.k --backend haskell --syntax-module IMP

%.imp.kore: %.imp imp-kompiled/definition.kore
	krun $< --dry-run

%.output: %.imp imp-kompiled/definition.kore
	krun $< --output-file $@

%.krun: %.imp imp-kompiled/definition.kore
	krun $<

%.test: %.output
	diff $< $<.golden

%.output.golden: %.output
	mv $< $<.golden

test: tests/sum.test tests/primes.test tests/collatz.test

golden: tests/sum.output.golden tests/primes.output.golden tests/collatz.output.golden

clean:
	rm -rf imp-kompiled tests/*.imp.kore tests/*.output
