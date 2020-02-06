Limitations of the current one-path implementation
==================================================

Both the one-path and the all-path algorithms assume the left hand side
and right hand side patterns of goals to be function-like. The one-path algorithm
applies rewrite rules to the goals using the `deriveSeq` procedure, which was not
designed to consider rule applications where two or more rules have the same LHS
(as in the case of non-deterministic semantics).
These characteristics of the implementation entail that the one-path algorithm,
while sound, doesn't guarantee full state space coverage.

TODO: example integration test; LHS is not function-like
TODO: `deriveSeq` with `φ → ◇w ψ`, `φ' → ● ψ₁`, `φ' → ● ψ₂`

