KORE_EXEC?="stack exec kore-exec --"
KOMPILE?=$(K_BIN)kompile
KRUN?=$(K_BIN)krun --haskell-backend-command $(KORE_EXEC)

demo-kompiled/definition.kore: demo.k
	$(KOMPILE) demo.k --backend haskell --syntax-module DEMO

%.demo.kore: %.demo demo-kompiled/definition.kore
	$(KRUN) $< --dry-run

%.output: %.demo demo-kompiled/definition.kore
	$(KRUN) $< --output-file $@

%.krun: %.demo demo-kompiled/definition.kore
	$(KRUN) $<

%.test: %.output
	diff $< $<.golden

%.output.golden: %.output
	mv $< $<.golden

test: tests/Nat.test tests/NatList.test tests/Truth.test

k-test: test

golden: tests/Nat.output.golden tests/NatList.output.golden tests/Truth.output.golden

clean:
	rm -rf demo-kompiled tests/*.demo.kore tests/*.output

.PHONY: k-test test golden clean %.test %.krun