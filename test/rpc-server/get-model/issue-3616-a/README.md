# `get-model` using a function with an smt-lemma

* Definition:
  - function `chop :: Int -> Int`, defined as `chop(X) => X modInt pow256`
  - `pow256` alias defined as the literal value of `2 ^ 256`

* Input: `chop(1 - x) == 0`
* Result: `Sat` with substitution `x = <value of pow256 + 1>`
