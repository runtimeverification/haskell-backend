# Introduction to the backend

## Data

### External representations

The external syntax of Kore is represented by types in the `Kore.Syntax` hierarchy.
The parser produces values of these types from the text of syntactically-valid Kore.
After parsing, the verifier (`Kore.ASTVerifier`) checks that the parsed values are well-formed
and converts the external representations into internal representations.

### `TermLike`

`TermLike` is the basic internal representation of Kore (matching logic) patterns.
The representation includes matching logic formulas, user-defined symbols and aliases, and built-in values.
`TermLike` is parameterized by the type of variables (actually variable _names_) which change during execution to carry extra information.

#### `Cofree` and `Synthetic`

`TermLike` is represented internally as a `Cofree` comonad (tree) over a base functor named `TermLikeF`.
`TermLikeF` is a sum type of all the pattern heads allowed in Kore, including built-ins.
The `Cofree` tree carries annotations at every node.
These annotations are synthetic attributes of the pattern and carry data used for various purposes.
The `Synthetic` typeclass ensures that the annotations are always kept updated, efficiently.

## Behavior
