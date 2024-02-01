These integration tests ensure that the pattern synonyms defined in `Booster.Pattern.Bool`, such as `AndBool`, actually match applications of the corresponding symbol (i.e. `_andBool_`, aka `Lbl'Unds'andBool'Unds'`) parsed from a freshly kompiled `definition.kore` using the version of K found in `deps/k_release`.

The main purpose of these tests is to make sure that changes to `definition.kore` and Booster's internal representation of it is in-sync when it comes to the pattern synonyms.

