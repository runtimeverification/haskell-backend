imp.kore:
	kompile imp.k --no-prelude --backend kore

%.imp.kore: %.imp imp.kore
	kast --kore $< > $<.kore

imp-kompiled: imp.k
	kompile imp.k

%.krun: %.imp imp-kompiled
	krun $<

%.korun: %.imp.kore
	stack exec -- kore-exec --run imp.kore --module IMP --pgm $<

clean:
	rm -rf imp.kore imp-kompiled tests/*.imp.kore
