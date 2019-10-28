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
The name `TermLike` alludes to the fact that these are _usually_ matching logic _terms_
(patterns that match at most one element).

#### `Cofree` and `Synthetic`

`TermLike` is represented internally as a `Cofree` comonad (tree) over a base functor named `TermLikeF`.
`TermLikeF` is a sum type of all the pattern heads allowed in Kore, including built-ins.
The `Cofree` tree carries annotations at every node.
These annotations are synthetic attributes of the pattern and carry data used for various purposes.
The `Synthetic` typeclass ensures that the annotations are always kept updated, efficiently.

#### `Builtin`

The backend supports these built-in sorts:

- `Int`: arbitrary-precision integers
- `Bool`
- `String`: packed strings
- `Bytes`: (work-in-progress) packed byte arrays
- `List`: associative lists
- `Map`
- `Set`

The `Int`, `Bool`, and `String` built-ins specialize ground terms in those domains for performance.
The `List`, `Map`, and `Set` collections specialize _expressions_ in those domains
both for performance and to facilitate unification and matching.

### `Condition`

A `Condition` represents the conditions or constraints along an execution path,
made up of a `Predicate` and a `Substitution`.

#### `Predicate`

`Predicate` is the representation predicate logic formulas,
essentially the subset of `TermLike` that can be built from `Ceil` and connectives.
`Predicate`s are the only type of pattern that can be translated for the external solver.

#### `Substitution`

A `Substitution` is a collection of `(variable, TermLike variable)` pairs
where `(x, t)` represents `\equals(x, t)`.
`Substitution` can be viewed as a specialization of `Predicate` in that way,
that is, a `Substitution` is the type of `Predicate` which can be applied as a substitution.

### `Pattern`

A `Pattern` is part of a program configuration:
some _term_ (`TermLike`) and the _condition_ on that term (`Condition`).
It is unusual to operate on a term without the accompanying condition,
so `Pattern` is somewhat more common than `TermLike` alone.

### `Conditional`

`Conditional` is a generalization of `Pattern`:
an arbitrary type with `Condition`s.

### `OrPattern`

`OrPattern` is a disjunction of `Pattern`s (program configurations).
This is the usual output of simplification.


## Behavior

### Unification

### Matching

### Semantic rules

### Function rules

### Simplification

### Refuting predicates
