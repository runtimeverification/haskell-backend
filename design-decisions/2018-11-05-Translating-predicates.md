Translating predicates for SMT
==============================

Background
----------

Symbolic execution relies on an external SMT solver to eliminate program
configurations that are conditioned on impossible predicates.

In ordinary propositional logic, predicates inhabit the sort `Bool`. Matching
logical predicates are more flexible: they are patterns in any sort `I` which
are either equal to `\top{I}()` or `\bottom{I}()`. Throughout this document, we
will use `I` as a distinguished sort variable indicating a predicate pattern of
arbitrary sort. Matching logic predicates can be recognized by the structure of
the pattern:

- `\top{I}()` and
- `\bottom{I}()` are constant predicates.
- `\ceil{S, I}(φ)` constructs a predicate in `I` from a pattern in `S`.
- The aliases (around `\ceil`) `\floor{S, I}(φ)`,
- `\equals{S, I}(φ₁, φ₂)`, and
- `\in{S, I}(φ₁, φ₂)` are predicates.
- The ordinary logical connectives `\and{I}(φ)`,
- `\or{I}(φ₁, φ₂)`,
- `\not{I}(φ)`,
- `\implies{I}(φ₁, φ₂)`, and
- `\iff{I}(φ₁, φ₂)` are predicates when their arguments are predicates,
- as are the quantifiers `\exists{I}(x:S, φ)` and
- `\forall{I}(x:S, φ)`.

Generally, we ask SMT to disprove predicates involving the builtin `Bool` and
`Int` sorts at the lowest level. However, matching logic allows these builtin
predicates to be lifted into any sort `I`. We must allow translating predicates
in arbitrary sorts so that the SMT solver has access to the entire predicate;
otherwise it is unlikely to have the information required to disprove it.

Problems
--------

Although matching logic's connectives share the names of the solver's
connectives, they operate differently in general. We are left with two problems:

1. How will we translate builtin `Bool` and `Int` predicates?
2. How will we translate arbitrary predicates?

Builtin translation
-------------------

Hooked symbols applied to the builtin `Bool` and `Int` sorts will be translated
directly using the corresponding SMT operations.

Builtin domain values (`\dv{Bool}` and `\dv{Int}`) are translated to the
corresponding literals in the solver.

Variables in the `Bool` and `Int` sorts are translated as variables in the
solver. (This is allowed because matching logic variables are single-valued.)

Equality defined by Kore `\equals{Bool, I}` and `\equals{Int, I}` is translated
to the SMT equality operation on `Bool` and `Int` respectively. The result of
the SMT operation inhabits sort `Bool`, which interacts with our decision below
to translate predicates in arbitrary matching logic sorts to the SMT `Bool`
sort. SMT equality corresponds to matching logic equality *only* for functional
patterns, so we take care to only translate functional patterns in builtin
sorts.

The matching logic connectives are *not* interpreted as connectives in the
solver because their interpretation differs. For example, consider that in
matching logic,
```
\and{Bool}(true{}(), false{}()) === \bottom{}()
```
whereas in the solver,
```
true ∧ false === false.
```

Arbitrary-sort translation
--------------------------

Predicates in arbitrary sorts are equal either to `\top{I}()` or `\bottom{I}()`,
so they can be represented in the solver's `Bool` sort.

`\top{I}()` and `\bottom{I}()` can be interpreted by the solver as `true` and
`false` respectively.

The matching logic connectives (`\and{I}`, `\or{I}`, `\not{I}`, `\implies{I}`,
`\iff{I}`) actually correspond to their counterparts in the solver, but only
operating on predicates. Therefore, these patterns are interpreted directly in
the solver when their children are predicates.

`\ceil{S, I}` and `\floor{S, I}` cannot be interpreted in the solver because
their children are not predicates. These patterns are predicates, so they are
translated as variables, i.e. left uninterpreted by the solver. `\in{S, I}` is
also translated as a variable. Identical patterns will be translated to the
same variable, so that the solver can reason over the predicates even if it
cannot reason under them.

As indicated above, `\equals{Bool, I}` and `\equals{Int, I}` are interpreted as
the corresponding builtin equalities. This is possible because the predicate in
`I` is translated to `Bool` in the solver. Equality on predicates (`\equals{I,
I}`) is translated as `\iff{I}`. Equality on all other sorts is translated to a
variable, i.e. left uninterpreted as `\ceil{S, I}`.

The quantifiers `\forall{I}` and `\exists{I}` cannot be interpreted in the
solver because we cannot generally introduce a solver variable in an arbitrary
sort. These patterns are translated as variables.

User-defined symbols and aliases should not occur as predicates except under an
uninterpreted construction such as `\ceil`. If a "bare" user-defined symbol or
alias occurs in a pattern, it cannot be translated as a predicate. This also
applies to the `\next` symbol and the `\rewrites` alias. Single-valued patterns
(variables and domain values) should not occur "bare" in a predicate and cannot
be translated.

Other solutions considered
--------------------------

We also considered to translate *only* symbols hooked to builtin sorts; however,
we need to send the entire predicate to SMT (if possible) so that the solver has
as much information as possible to disprove the condition. In practice, the
solver would not be able to refute even simple program configurations without
translating arbitrary-sort predicates.
