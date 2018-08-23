demo.kore: demo.k
	kompile demo.k --backend kore --syntax-module DEMO

%.demo.kore: %.demo demo.kore
	kast --kore $< > $<.kore

%.output: %.demo.kore demo.kore
	stack exec -- kore-exec demo.kore --module DEMO --pattern $< > $>

%.korun: %.output
	cat $<

%.test: %.output
  diff $< $<.golden

test: test/Nat.test test/NatList.test test/Truth.test

clean:
	rm -rf demo.kore demo-kompiled test/*.demo.kore test/*.output