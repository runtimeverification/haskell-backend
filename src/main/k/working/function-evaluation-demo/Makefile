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

test: tests/Nat.test tests/NatList.test tests/Truth.test

golden: tests/Nat.output.golden tests/NatList.output.golden tests/Truth.output.golden

clean:
	rm -rf demo.kore demo-kompiled tests/*.demo.kore tests/*.output
