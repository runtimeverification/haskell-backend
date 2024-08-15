These tests were collected from pyk integration tests, see: https://github.com/runtimeverification/k/blob/04d55ad993e9afb3d0d57ab8233d674eb4745c77/pyk/src/tests/integration/proof/test_implies_proof.py#L31-L67 :

# antecedent-bottom

contains `"3" <Int VarX:SortInt{}` and `VarX:SortInt{} <Int "3"` in the antecedent. Expected response is a `#Bottom` condition

# consequent-constraint

Antecedent contains

```
... "$n" = "3"; ...
```

consequent contains

```
... "$n" = VarX:SortInt{}; ...
```
and the condition `VarX:SortInt{} <Int "3"`

Kore correctly returns invalid, sice it matches `VarX = "3"`, which together with `VarX:SortInt{} <Int "3"` is proved invalid by Z3.
Booster currently aborts, because it cannot prove `VarX:SortInt{} <Int "3"` or that the constraints are `#Bottom`. This would require turning the substitution into predicates and passing those to Z3.


# refutation-{1,3,4}

These tests do not currently work in booster because they involve existential variables in the RHS with side-conditions which are decided via Z3, e.g.:

```
VarX:SortInt{} <Int VarY:SortInt{}
VarZ:SortInt{} <Int VarX:SortInt{}
VarY:SortInt{} <Int VarZ:SortInt{}
```

Until booster does a full check like kore, these will remain unsupported. They do not seem to appear much in real world proofs.
