demo.kore: demo.k
	kompile demo.k --backend kore --syntax-module DEMO

%.demo.kore: %.demo demo.kore
	kast --kore $< > $<.kore

%.korun: %.demo.kore demo.kore
	stack exec -- kore-exec demo.kore --module DEMO --pattern $<

clean:
	rm -rf demo.kore demo-kompiled *.demo.kore