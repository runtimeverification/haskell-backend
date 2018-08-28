imp.kore: imp.k
	kompile imp.k --backend kore --syntax-module IMP

%.imp.kore: %.imp imp.kore
	kast --sort K --kore $< > $<.kore

%.output: %.imp.kore imp.kore
	stack exec -- kore-exec imp.kore --module IMP --is-program --pattern $< > $@

%.korun: %.output
	cat $<

%.output.golden: %.output
	mv $< $<.golden

%.test: %.output
	diff $< $<.golden

test: tests/sum.test tests/primes.test tests/collatz.test

golden: tests/sum.output.golden tests/primes.output.golden tests/collatz.output.golden

clean:
	rm -rf imp.kore imp-kompiled tests/*.imp.kore tests/*.output
