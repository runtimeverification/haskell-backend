demo-kompiled/definition.kore: demo.k
	kompile demo.k --backend haskell --syntax-module DEMO

%.demo.kore: %.demo demo-kompiled/definition.kore
	krun $< --dry-run

%.output: %.demo demo-kompiled/definition.kore
	krun $< --output-file $@

%.krun: %.demo demo-kompiled/definition.kore
	krun $<

%.test: %.output
	diff $< $<.golden

%.output.golden: %.output
	mv $< $<.golden

test: tests/Nat.test tests/NatList.test tests/Truth.test

golden: tests/Nat.output.golden tests/NatList.output.golden tests/Truth.output.golden

clean:
	rm -rf demo-kompiled tests/*.demo.kore tests/*.output
