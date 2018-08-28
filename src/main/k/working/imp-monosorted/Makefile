imp.kore: imp.k
	kompile imp.k --backend kore --syntax-module IMP

%.imp.kore: %.imp imp.kore
	kast --kore $< > $<.kore

%.output: %.imp.kore imp.kore
	stack exec -- kore-exec imp.kore --module IMP --is-program --pattern $< > $@

%.korun: %.output
	cat $<

%.test: %.output
	diff $< $<.golden

test: tests/sum.test tests/primes.test tests/collatz.test

golden: tests/sum.output tests/primes.output tests/collatz.output
	mv tests/sum.output tests/sum.output.golden
	mv tests/primes.output tests/primes.output.golden
	mv tests/collatz.output tests/collatz.output.golden

clean:
	rm -rf imp.kore imp-kompiled tests/*.imp.kore tests/*.output
