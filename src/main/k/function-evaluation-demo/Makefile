demo.kore: demo.k
	kompile demo.k --backend kore --syntax-module DEMO

%.korun: %.demo demo.kore
	stack exec -- kore-exec --run imp.kore --module IMP --pattern $<

clean:
	rm -rf demo.kore demo-kompiled