demo.kore: demo.k
	kompile demo.k --backend kore --syntax-module DEMO

%.demo.kore: %.demo demo.kore
	kast --kore $< > $<.kore

%.output: %.demo.kore demo.kore
	stack exec -- kore-exec demo.kore --module DEMO --pattern $< > $@

%.korun: %.output
	cat $<

%.test: %.output
	diff $< $<.golden

%.output.golden: %.output
	mv $< $<.golden

test: tests/1.test tests/2.test tests/3.test tests/4.test

golden: tests/1.output.golden tests/2.output.golden tests/3.output.golden tests/4.output.golden

clean:
	rm -rf demo.kore demo-kompiled tests/*.demo.kore tests/*.output
