# Introduction to the Haskell backend

## Data

### External representations

The external syntax of Kore is represented by types in the `Kore.Syntax` hierarchy.
The parser produces values of these types from the text of syntactically-valid Kore.
After parsing, the verifier (`Kore.Validate`) checks that the parsed values are well-formed
and converts the external representations into internal representations.

References:

- `Kore.Syntax.Pattern`
- `Kore.Syntax.Definition`
- `Kore.Validate.DefinitionVerifier`

### `TermLike`

`TermLike` is the basic internal representation of Kore (matching logic) patterns.
The representation includes matching logic formulas, user-defined symbols and aliases, and built-in values.
`TermLike` is parameterized by the type of variables (actually variable _names_) which change during execution to carry extra information.
The name `TermLike` alludes to the fact that these are _usually_ matching logic _terms_
(patterns that match at most one element).

References:

- `Kore.Internal.TermLike`

#### `Cofree` and `Synthetic`

`TermLike` is represented internally as a `Cofree` comonad (tree) over a base functor named `TermLikeF`.
`TermLikeF` is a sum type of all the pattern heads allowed in Kore, including built-ins.
The `Cofree` tree carries annotations at every node.
These annotations are synthetic attributes of the pattern and carry data used for various purposes.
The `Synthetic` typeclass ensures that the annotations are always kept updated, efficiently.

References:

- `Kore.Attribute.Synthetic`
- `Kore.Attribute.Pattern`
- `Control.Comonad.Trans.Cofree`

#### `Builtin`

The backend supports these built-in sorts:

- `Int`: arbitrary-precision integers
- `Bool`
- `String`: packed strings
- `Bytes`: (work-in-progress) packed byte arrays
- `List`: associative lists
- `Map`
- `Set`

The `Int`, `Bool`, `String`, and `Bytes` built-ins specialize ground terms in those domains for performance.
The `List`, `Map`, and `Set` collections specialize _expressions_ in those domains
both for performance and to facilitate unification and matching.

References:

- `Kore.Domain.Builtin`

### `Condition`

A `Condition` represents the conditions or constraints along an execution path,
made up of a `Predicate` and a `Substitution`.

References:

- `Kore.Internal.Condition`

#### `Predicate`

`Predicate` is the representation predicate logic formulas,
essentially the subset of `TermLike` that can be built from `Ceil` and connectives.
`Predicate`s are the only type of pattern that can be translated for the external solver.

References:

- `Kore.Internal.Predicate`

#### `Substitution`

A `Substitution` is a collection of `(variable, TermLike variable)` pairs
where `(x, t)` represents `\equals(x, t)`.
`Substitution` can be viewed as a specialization of `Predicate` in that way,
that is, a `Substitution` is the type of `Predicate` which can be applied as a substitution.

References:

- `Kore.Internal.Substitution`

### `Pattern`

A `Pattern` is part of a program configuration:
some _term_ (`TermLike`) and the _condition_ on that term (`Condition`).
It is unusual to operate on a term without the accompanying condition,
so `Pattern` is somewhat more common than `TermLike` alone.

References:

- `Kore.Internal.Pattern`

### `Conditional`

`Conditional` is a generalization of `Pattern`:
an arbitrary type with `Condition`s.

References:

- `Kore.Internal.Conditional`

### `OrPattern`

`OrPattern` is a disjunction of `Pattern`s (program configurations).
This is the usual output of simplification.

References:

- `Kore.Internal.OrPattern`


## Behavior

### Unification

Unification is represented in matching logic by `\and`
and is essentially implemented as `\and` simplification,
that is, by pushing `\and` down through symbols as far as possible.
The backend has special support for unification modulo certain theories:

- Constructors (injective, no-confusion)
- Sort injections (constructors modulo triangle equality)
- Overloaded symbols
- `List` (common patterns only)
- `Map` (common patterns only)
- `Set` (common patterns only)

Because unification is implemented as "pushing `\and` down", the solution is determined in parallel.
Consider this example unification, with a constructor `C(_, _)` and constant terms `a` and `b` which may be undefined:

```
C(x, x) ∧ C(a, b)
C(x ∧ a, x ∧ b)                                    -- constructor axioms: injectivity
C(a ∧ (\ceil(a) ∧ x = a), b ∧ (\ceil(b) ∧ x = b))  -- singular variables
C(a, b) ∧ (\ceil(a) ∧ \ceil(b)) ∧ (x = a ∧ x = b)  -- lifting conditions
C(a, b) ∧ (\ceil(a) ∧ \ceil(b)) ∧ x = a ∧ b        -- substitution normalization
C(a, b) ∧ (\ceil(a) ∧ \ceil(b)) ∧ x = (a ∧ a = b)  -- substitution normalization
C(a, b) ∧ (\ceil(a) ∧ \ceil(b) ∧ a = b) ∧ x = a    -- substitution normalization
```

Disjunction is handled by distribution.
The substitution normalization step is discussed below.

References:

- `Kore.Simplify.AndTerms`
- `Kore.Builtin.List`
- `Kore.Builtin.Map`
- `Kore.Builtin.Set`

### Substitution normalization

Substitution normalization is a step after unification required by unifying in parallel.
Normalization solves two problems:
first, a substitution variable may be duplicated (occurs on the left-hand side of multiple substitutions),
and second, there may be a cycle in the substitution (`x = f(y) ∧ y = g(x)`).

A duplicated substitution is solved by unification:

```
x = t₁ ∧ ... ∧ x = tₙ
x = (t₁ ∧ ... ∧ tₙ)
x = t ∧ ...
```

Unification of the right-hand sides may produce additional conditions and substitutions,
so the deduplication process iterates until no duplications remain.

After the substitutions are deduplicated, they are topologically sorted by their dependencies on each other.
If a cycle exists, we determine if that cycle passes through any simplifiable symbols.
If the cycle passes only through constructors or other non-simplifiable symbols,
and it involves any element variables,
then the result of normalization is `\bottom`.
If a non-simplifiable cycle involves only set variables,
those variables themselves are equated with `\bottom`.
If the cycle passes through simplifiable symbols,
the cycle (denormalized part) is held as conditions apart from the rest of the substitution.
In any case, the normalizable part of the substitution is ordered and each substitution is applied to the others
so that no variable occuring on the right-hand side of any substitution also occurs on the left-hand side of any (other) substitution.

The denormalized part of a substitution is handled differently in the context of unification and simplification.
During unification, a denormalized substitution is considered an error
because we have failed to produce a substitution which unifies the given patterns.
During predicate simplification, we are more flexible;
it is entirely reasonable to generate conditions such as `x = x + y` in this context.

References:

- `Kore.Unification.SubstitutionNormalization`
- `Kore.Simplify.SubstitutionSimplifier`

### Matching

An ad hoc subset of patterns can be matched, based on the usual needs of the frontend and semantics developers.
Matching is implemented sequentially, so there is no separate substitution normalization step.

References:

- `Kore.Rewrite.Axiom.Matcher`

### Semantic rules

Semantic rules are applied by the following procedure:

1. Unify (as described above) the left-hand side of the rule with the current configuration's term.
1. Conjoin the `requires` clause with the unification conditions and simplify.
1. Conjoin with the initial conditions (from the current configuration) and simplify.
1. Check that the conditions include substitutions for every variable on the left-hand side of the rule.
1. Conjoin with the `ensures` clause.
1. Instantiate the rule with the combined conditions.
1. Calculate the _remainder_ from the (unification+requires) conditions of all applied rules.

The procedures to apply one-path and all-path reachability claims is described in other documents.

References:

- `Kore.Rewrite.Step`

### Function rules

Function rules are instantiated by matching, as described above.
Function evaluation occurs during simplification, but not during unification.
Function evaluation _may_ split the configuration
if multiple branches of a function's definition match the configuration;
this point is planned to change.

References:

- `Kore.Rewrite.Function.Evaluator`
- `Kore.Rewrite.Axiom.EvaluationStrategy`

### Simplification

Patterns are simplified from the bottom up.
The top-level condition of the configuration is passed down as context for function and predicate evaluation.
New conditions are accumulated as simplification moves up the syntax tree,
requiring substitution normalization at the top.
`TermLike` is simplified in a single pass, but this is planned to change.
`Condition` is simplified in a loop where new substitutions are applied and the result is re-simplified.

References:

- `Kore.Simplify.TermLike`
- `Kore.Simplify.Condition`

### Refuting predicates

Some predicates can be evaluated by an external solver;
in theory this can be any solver with an SMT-LIB 2 interface, but in practice we use Z3.
Generally, we only check satisfiability of a predicate,
using the solver to refute impossible execution paths.
Predicate logic connectives are translated to their corresponding connectives in the solver.
`\equals` can be translated if its arguments are in `Int` or `Bool`.
It is essential that the arguments be functional (match exactly one value)
because of the solver's internal assumptions.
Other predicates cannot be translated directly,
but they are translated as unknown (uninterpreted) `Bool` variables.
An uninterpreted predicate is translated as the same variable wherever it occurs in a formula
so that the solver can refute predicates such as `\in(a, b) ∧ \not \in(a, b)`.

The backend uses a single solver process for all queries.
The solver is initialized with all the symbols and sorts defined by the user
and many axioms (such as constructor axioms).
While proving, queries are sent to the solver incrementally,
avoiding the overhead of restarting the solver for each query.

References:

- `Kore.Rewrite.SMT.Translate`
- `Kore.Rewrite.SMT.Evaluator`
