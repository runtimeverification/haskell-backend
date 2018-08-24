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

clean:
	rm -rf imp.kore imp-kompiled tests/*.imp.kore tests/*.output
