.PHONY: clean golden test

tests = sum-to-n-spec.kprove
diffs = $(foreach test, $(tests), $(test).diff)
actuals = $(foreach test, $(tests), $(test).actual)

clean:
	rm -f $(diffs) $(actuals)

golden: $(foreach test, $(tests), $(test).golden)

test: $(diffs)

%.diff: %.actual
	diff -u $*.golden $< >$@

sum-to-n-spec.kprove.actual: KPROVE_OPTS = -m VERIFICATION

%.kprove.actual: %.k
	$${KEVM_DIR:?}/kevm prove --backend haskell $< $(KPROVE_OPTS) >$@ $(PARTIAL)

%.kprove.golden: %.kprove.actual
	mv $< $@
