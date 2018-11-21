Unification
===========

Background
----------

Whenever we want to apply an axiom `∀ Y . α(Y) -> •β(Y)` to a pattern `φ(X)`
we have to find the pattern that contains whatever is common to `α(Y)`
and `φ(X)` (i.e. their intersection, a.k.a. `φ(X) ∧ α(Y)`) and use that,
together with `β(Y)` to compute a pattern `φ'(X)` such that `φ(X) -> •φ'(X)`.

In practice, we want to find a term pattern `t(x)`, preferably composed out of
variables, constructors, functions and similar things,
a substitution `S(X, Y)` and a predicate `P(X)` such that
`φ(X) ∧ α(Y) = t(X) ∧ S(X, Y) ∧ P(X)`.

It is debatable whether we want to have substitutions for the `X` variables.

Problem
-------

* Deciding if there are `t(X)`, `S(X, Y)` and `P(X)` such that
  `φ(X) ∧ α(Y) = t(X) ∧ S(X, Y) ∧ P(X)`, i.e. finding if `φ(X)` and `α(Y)`
  *unify*.
* Actually finding those patterns.

Additional constraints and assumptions
--------------------------------------

* Note that one can't just ignore `t(X)` and use `S(X, Y)` and `P(X)`,
  because `t(X)` may be `⊥`, but it's safe to use
  `S(X, Y)` and `P(X) ∧ ⌈t(X)⌉`. Indeed, many of the unification cases
  explicitly use `⌈φ(X) ∧ α(Y)⌉`.
* The unification algorithm assumes that it mostly unifies term patterns, i.e.
  it usually works only with variables and functional symbols, but,
  in some cases, it can allow other symbols and logical operators.
* We are only interested in substitutions that resolve the entire `Y`.
* We will assume that infinite constructor-based recursion can't exist,
  e.g. `[x = C(x)]` is bottom.
* We will give up if we have infinite recursion based on things other than
  constructors, e.g. `[x = f(x)]`.
* Whenever we give up (i.e. because we don't know how how to handle something),
  we will return bottom instead of signaling an error.

Solution
--------

Note that it is not always possible to determine if two patterns unify.
The algorithm below describes some of the cases when this is possible.

The algorithm works in a top-down fashion, but since unification
can't always be resolved efficiently locally
(think `concat(X, Y->Z)` unified with a concrete map, where we'd like
to resolve the `Y` variable before the unification), we represent
things that should normally be substitutions as predicates, and, at various
points in the algorithm, we try to transform them into substitutions.
The exact points where this happens are left open (current implementation
does this whenever we merge substitutions and predicates).

The algorithm has a list of algorithms for the cases where it knows how
to solve unification. Each such algorithm is expected to return:
* *not-handled-error* if it does not know how to handle the provided patterns
* *handled-with-error* if it knows how to handle the provided patterns,
  but there was an error not specific to the current algorithm (e.g. children's
  unification failed with error).
* *bottom* if it knows how to handle the patterns, but unification is
  impossible (e.g. it tries to unify different constructors).
* a *pattern* of the form `t(X) ∧ S(X, Y) ∧ P(X)` if unification succeeded.

Then the algorithm looks like this:

```
unify(p1, p2):
  for unifier in known-unification-algorithms
    case unifier(p1, p2) of
      not-handled-error -> continue
      handled-with-error -> return handled-with-error
      bottom -> return bottom
      pattern -> return pattern
  return handled-with-error  -- counterintuitive, but makes things easier.
```

Known unification cases
-----------------------

The order of these cases in the `known-unification-algorithms` list is
important both for optimization purposes and because, in practice,
later cases rely on being called only when some of the previous cases fail
(they could retest the previous cases' conditions, but, for simplicity,
they don't).

### bool and

Resolves unification with top and bottom patterns.

```
T ∧ φ = φ
φ ∧ T = φ
⊥ ∧ φ = ⊥
φ ∧ ⊥ = ⊥
not-handled-error otherwise
```

### equal patterns

Resolves the unification of two identical patterns. Currently
it tests for actual equality and not for alpha equivalence.

```
φ ∧ φ = φ
not-handled-error otherwise
```

### variable vs function-like pattern

Creates a substitution for that variable and pattern. If the functional pattern
is also a variable, the substitution maps the lower variable to the higher one (using the default variable order). This has two uses:
* The callers use it to substitute axiom variables for pattern variables
  whenever there is a choice.
* The substitution normalization algorithm can work under the assumption that
  we don't have both `x->y` and `y->x` as substitutions.

Note that, at first sight, this should work only for functional patterns, not
for random function-like patterns. However, the unification result is
`f ∧ [x -> f]`, which, if we check it carefully, is equal to `x ∧ f` for all
function-like patterns `f`.

```
x ∧ y = y ∧ [x -> y]
y ∧ x = y ∧ [x -> y]  -- because of the order test mentioned above
x ∧ φ
  | if φ is function-like    = φ ∧ [x -> φ]
  | otherwise                = not-handled-error
```

### function-like pattern vs variable

The same as above, but reversing the pattern-variable order.

### equal injective heads

```
σ(φ1, φ2, ..., φn) ∧ σ(ψ1, ψ2, ..., ψn)
  | if `σ` is injective    = σ(φ1 ∧ ψ1, φ2 ∧ ψ2, ..., φn ∧ ψn)
  | otherwise              = not-handled-error
```

The evaluation of `σ(φ1 ∧ ψ1, φ2 ∧ ψ2, ..., φn ∧ ψn)` goes like this:

```
evaluate each φi ∧ ψi by calling unify(φi, ψi)
if the result is an error, return handled-with-error
if the result is ⊥, return ⊥  -- actually handled through the general
                              -- case below.
Otherwise, represent the result as ti ∧ si ∧ pi

return σ(t1, t2, ..., tn) ∧ (s1 ∧ s2 ∧ ... ∧ sn) ∧ (p1 ∧ p2 ∧ ... ∧ pn)
```

### Distinct sort injections

Does not actually test for the distinctness part, assumes that the
"equal injective heads" case was checked before

```
inj(s2, s1)(φ) ∧ inj(s3, s1)(ψ)
  | if s2 is a subsort of s3            = inj(s3, s1)(inj(s2, s3)(φ) ∧ ψ)
  | if s3 is a subsort of s2            = inj(s2, s1)(φ ∧ inj(s3, s2)(ψ))
  | if φ or ψ are constructor-like      = ⊥
  | if s2 and s3 have no common subsort = ⊥
  | otherwise                           = crash with error message

not-handled-error otherwise
```

In this context, "constructor-like" means that the pattern behaves like a
constructor-based one, i.e. it can't be equal to a sort injection.
Examples include patterns having constructors at the top and domain values.

### Constructor vs sort injection

```
Constr(φ1, φ2, ..., φn) ∧ inj(s2, s1)(ψ) = ⊥
inj(s2, s1)(ψ) ∧ Constr(φ1, φ2, ..., φn) = ⊥

not-handled-error otherwise
```

### Different constructors

Does not actually test for the distinctness part, assumes that the
"equal injective heads" case was checked before

```
Constr1(φ1, φ2, ..., φn) ∧ Constr2(ψ1, ψ2, ..., ψn) = ⊥

not-handled-error otherwise
```

### Builtin map unification

Note that currently map keys cannot have variables, so it does not make sense
to worry about alpha equivalence.

```
{k1 -> φ1, k2 -> φ2, ..., km -> φm} ∧ {l1 -> ψ1, l2 -> ψ2, ..., ln -> ψn}
  | if {k1, k2, ..., km} ≠ {l1, l2, ..., ln}
    = ⊥
  | otherwise
    = {k1 -> φ1 ∧ ψ1, k2 -> φ2 ∧ ψ2, ..., kn -> φn ∧ ψn}

{k1 -> φ1, k2 -> φ2, ..., km -> φm}
    ∧ concat({l1 -> ψ1, l2 -> ψ2, ..., ln -> ψn}, x)
  | if {l1, l2, ..., ln} ⊄ {k1, k2, ..., kn}
    = ⊥
  | otherwise
    = {k1 -> φ1 ∧ ψ1, k2 -> φ2 ∧ ψ2, ..., km -> φm ∧ ψm}
      ∧ x = {lm+1 -> ψm+1, ..., ln -> ψn}
      renumbering such that {l1, l2, ..., lm} = {k1, k2, ..., km}
      (see below for how the {k1 -> φ1 ∧ ψ1, ...} map is evaluated)

{k1 -> φ1, k2 -> φ2, ..., km -> φm}
    ∧ concat(x, {l1 -> ψ1, l2 -> ψ2, ..., ln -> ψn})
  = identical to the above

dv ∧ concat(ψ1, ψ2)
  = dv ∧ ⌈dv ∧ concat(ψ1, ψ2)⌉   -- ** different from the actual implementation.
    where dv = {k1 -> φ1, k2 -> φ2, ..., km -> φm}

{k1 -> φ1, k2 -> φ2, ..., km -> φm} ∧ element(l, ψ)
  | if m > 1     = ⊥
  | otherwise    = {k1 ∧ l -> φ1 ∧ ψ}

ψ ∧ {k1 -> φ1, k2 -> φ2, ..., km -> φm}
  = {k1 -> φ1, k2 -> φ2, ..., km -> φm} ∧ ψ

not-handled-error otherwise
```

The evaluation of `{k1 -> φ1 ∧ ψ1, k2 -> φ2 ∧ ψ2, ..., kn -> φn ∧ ψn}`
is similar to the evaluation for equal injective heads and goes like this:

```
evaluate each φi ∧ ψi by calling unify(φi, ψi)
if the result is an error, return handled-with-error
if the result is ⊥, return ⊥  -- actually handled through the general
                              -- case below.
Otherwise, represent the result as ti ∧ si ∧ pi

return {k1 -> t1, k2 -> t2, ..., kn -> tn}
       ∧ (s1 ∧ s2 ∧ ... ∧ sn)
       ∧ (p1 ∧ p2 ∧ ... ∧ pn)
```

Note that the actual implementation uses `φi` instead of `ti` in the return
value above.

The evaluation of `{k1 ∧ l -> φ1 ∧ ψ}` is similar.

### Builtin set unification

Note that currently set elements cannot have variables, so it does not
make sense to worry about alpha equivalence.

```
{k1, k2, ..., km} ∧ {l1, l2, ..., ln}
  | if {k1, k2, ..., km} ≠ {l1, l2, ..., ln}    = ⊥
  | otherwise                                   = {k1, k2, ..., kn}

{k1, k2, ..., km} ∧ concat({l1, l2, ..., ln}, x)
  | if {l1, l2, ..., ln} ⊄ {k1, k2, ..., km}
    = ⊥
  | otherwise
    = {k1, k2, ..., kn} ∧ x = {kn+1, ..., km}
    where elements are renumbered such that {l1, ..., ln} = {k1, ..., kn}

{k1, k2, ..., km} ∧ concat(x, {l1, l2, ..., ln})
  = same as above

dv ∧ concat(ψ1, ψ2)
  = dv ∧ ⌈dv ∧ concat(ψ1, ψ2)⌉   -- ** different from the actual implementation.
    where dv = {k1, k2, ..., km}

{k1, k2, ..., km} ∧ element(l)
  | if m > 1     = ⊥
  | otherwise    = {k ∧ l}

ψ ∧ {k1 -> φ1, k2 -> φ2, ..., km -> φm}
  | if ψ is an application pattern   -- ** different from map and list handling.
    = {k1 -> φ1, k2 -> φ2, ..., km -> φm} ∧ ψ

not-handled-error otherwise
```

### Builtin list unification

```
[k1, k2, ..., km] ∧ [l1, l2, ..., ln]
  | if m ≠ n     = ⊥
  | otherwise    = [k1 ∧ l1, k2 ∧ l2, ..., kn ∧ ln]
    see below for how this list is evaluated.

[k1, k2, ..., km] ∧ concat([l1, l2, ..., ln], x)
  | if n > m     = ⊥
  | otherwise    = [k1 ∧ l1, k2 ∧ l2, ..., kn ∧ ln] ∧ x = [kn+1, ..., km]

[k1, k2, ..., km] ∧ concat(x, [l1, l2, ..., ln])
  | if n > m     = ⊥
  | otherwise    = [km-n+1 ∧ l1, km-n+2 ∧ l2, ..., km ∧ ln] ∧ x = [k1, ..., kn]

dv ∧ concat(ψ1, ψ2)
  = dv ∧ ⌈dv ∧ concat(ψ1, ψ2)⌉   -- ** different from the actual implementation.
    where dv = [k1, k2, ..., km]

ψ ∧ {k1 -> φ1, k2 -> φ2, ..., km -> φm}
  = {k1 -> φ1, k2 -> φ2, ..., km -> φm} ∧ ψ

not-handled-error otherwise
```


### Domain values vs constructors

```
Constr(φ1, φ2, ..., φn) ∧ DV = ⊥
DV ∧ Constr(φ1, φ2, ..., φn) = ⊥

not-handled-error otherwise
```

### Different domain values

Does not test for distinctness, assumes that the "equal patterns" case
was already checked.

```
DV ∧ DV = ⊥

not-handled-error otherwise
```

### Different string literals

Does not test for distinctness, assumes that the "equal patterns" case
was already checked.

```
S1 ∧ S2 = ⊥

not-handled-error otherwise
```

### Different char literals

Does not test for distinctness, assumes that the "equal patterns" case
was already checked.

```
C1 ∧ C2 = ⊥

not-handled-error otherwise
```

### Different function-like patterns

Does not test for distinctness, assumes that the "equal patterns" case
was already checked.

```
φ ∧ ψ
  | if φ and ψ are function-like    = φ ∧ (φ == ψ)
  | otherwise                       = not-handled-error
```
