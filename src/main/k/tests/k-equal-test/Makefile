eqtest.kore: eqtest.k
	kompile eqtest.k --backend kore --syntax-module EQTEST

%.eqtest.kore: %.eqtest eqtest.kore
	kast --kore $< > $<.kore

%.output: %.eqtest.kore eqtest.kore
	stack exec -- kore-exec eqtest.kore --module EQTEST --pattern $< --sort K> $@

%.korun: %.output
	cat $<

%.test: %.output
	diff $< $<.golden

test: test/eq.test test/neq.test

clean:
	rm -rf eqtest.kore eqtest-kompiled tests/*.eqtest.kore tests/*.output
