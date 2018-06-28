demo.kore: demo.k
	kompile demo.k --backend kore --syntax-module DEMO

%.run: %.demo demo.kore
	stack exec -- kore-parser demo.kore --verify --print --pattern $< --module DEMO --evaluate 2>&1 | sed 's/Lbl//g;s/()//g;s/,Cons/,\nCons/g;s/,Nil/,\nNil/g'

clean:
	rm -rf demo.kore demo-kompiled