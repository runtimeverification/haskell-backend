# Testing `get-model` in the presence of subsorting

This test was extracted from a failing get-model call (https://github.com/runtimeverification/haskell-backend/issues/3917), 
where the booster was sending an equality between two variables of different sorts.
Since Z3 does not support subsorts, we need to make sure any terms containing injections are abstracted away behind a variable and the injection
doesn't get removed.