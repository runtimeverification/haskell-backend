Decision Template
=================

Background
----------

In order to evaluate expressions, usually one has to evaluate the
expression terms first, then the expression itself is evaluated. As
an example, `(1+2)+(3+4)` may be evaluated, in order, to the following
equivalent patterns, where `[]` is a placeholder for an expression that was extracted from a larger one for evaluation, while `~>` separates expressions
to be evaluated:
```
(1+2)+(3+4)
1+2 ~> []+(3+4)  -- heating
3 ~> []+(3+4)    -- rewriting
3+(3+4)          -- cooling
3+4 ~> 3+[]      -- heating
7 ~> 3+[]        -- rewriting
3+7              -- cooling
10               -- rewriting
```

In many cases it is desirable to allow expressions to be evaluated in a fairly
free order. Consider the following C example:
```
(f() + g()) + h()
```
where `f`, `g` and `h` have side effects. According to the standard, these
functions can be called in any order, e.g. it is valid to call `g`, then `h`,
then `f`.

In all-path reachability proofs one attempts to show that, when starting from
a given pattern, no matter how it is evaluated, one reaches a certain
target pattern.

In coinductive proofs, whenever there is a cycle in which a pattern can be
rewritten, indirectly or not, to itself, anything can be proven.

Problem/Questions
-----------------

How to encode the heating and cooling rules in kore, in such a way that there
are no rewrite cycles, we can compute all patterns reachable from a given one,
and we can prove that only those are reachable, while allowing any evaluation
order for the heated/cooled terms when that's desirable.

Decision: Use equations.
------------------------

Use rewriting rules like the following, where `~>` is a function symbol:

```
inj{Exp, K}(a+b) = inj{Exp, K}(a) ~> []+b
inj{Exp, K}(a+b) = inj{Exp, K}(b) ~> a+[]
```

The "Using rewriting rules with "changed" bit" solution would have also
solved most of the problems.

Reasoning and other options considered
--------------------------------------

Options that were considered:

### Using plain rewriting rules

Using rules like the following generates rewrite cycles:
```
a+b => a ~> []+b
a+b => b ~> a+[]
a ~> []+b => a+b
b ~> a+[] => a+b
```

### Using rewriting rules with side conditions

```
a+b => a ~> []+b   if a is not a value
a+b => b ~> a+[]   if b is not a value
a ~> []+b => a+b   if a is a value
b ~> a+[] => a+b   if b is a value
```

Side conditions solve the rewrite cycle issue, but do not allow all possible
expression evaluations, e.g. it does not allow evaluating `g`, then `h`, then
`f` in the Background section example.

### Using equations, e.g.
```
a+b = a ~> []+b
a+b = b ~> a+[]
```

These solve the evaluation order issue in an elegant way, and it is
usually computationally feasible to compute all possible expression expansions.

There are a few problems though. First, note that if we have
`a+b = a ~> []+b` and `+` is a constructor, then `~>` can't be a constructor.

This makes unification more difficult: whenever we try to unify `~>` we must
expand the terms we have using all possible equations, then we need to match
the top form as if it would be a constructor, and continue unifying the
children. As an example, if we unify `(a+b)+c~>something` with `x+y ~> z`
we may expand the former to the following set
```
(a+b)+c~>something
a+b~>[]+c~>something
a~>[]+b~>[]+c~>something
b~>a+[]~>[]+c~>something
c~>(a+b)+[]~>something
```
And then we would have the following unifications:
```
[x=a+b, y=c, z=something]
[x=a, y=b, z=[]+c~>something]
⊥
⊥
⊥
```

A second problem would be that equations can be applied anywhere, so we could
also have `(a~>[]+b)+c~>something` as an expansion. This is not helpful in any
way, but we could try to heat only things at the top, i.e.
`<k> a+b </k> = <k> a ~> []+b </k>` or, using sort injections,
`inj{Exp, K}(a+b) = inj{Exp, K}(a) ~> []+b`. Depending on how we define
the symbols involving `[]`, we may or may not need `inj` around `[]+b`.

With the former option, if `<k>` is a constructor, then the
equation above is equivalent to the original one, `a+b = a ~> []+b`, and we
are back to the weird expansions problem. So it seems that `<k>` should
not be a constructor, while `~>` can be one.

Actually, we have a more general problem, i.e. how can we be sure that,
given a set of equations, we have inferred all that we can, and, preferably,
we would like to know that we can't get contradictions from those equations.

We can simplify the problem by expanding the symbols by-need. We could
always expand patterns fully before rewriting, then we can unify functions
as if they would be constructors, but the result would be too messy, and
we may expand parts of a pattern that are not needed for the current rule.

It is probably better to expand only when needed, i.e. in the
unification algorithm. Whenever we have to unify a non-constructor symbol, e.g.
`~>`, with something else, we expand the non-constructor at the top
and all its children that have non-constructors at the top, and their
non-constructor children, and so on.

Note that the above requires that at least one of the equality terms has
a non-constructor at the top.

Probably we want to cache the expansion results and reuse them for future
unifications, and we want to be able to merge various rewriting branches.

This also helps to check that we don't infer unwanted stuff, see the
`Unwanted inferences` subsection.

My guess is that we want to expand when needed and cache the results.

A third problem is that it seems rather difficult to prove that one needs
to consider only rewrites starting from those expansions if one wants to
find if we reach the target pattern no matter how we evaluate and rewrite
the start pattern.

However, it might be possible to prove this at the meta level, so we
will assume that this problem is somewhat solvable.

#### Unwanted inferences

If we know all equations that can be applied when expanding a given term,
we might have an easier time finding out if they have any issues.

As an impractical example, if our equations have non-constructors
only at the top, and they only have terms made out of symbols,
variables and domain values (we might be able to include more things here),
then we can replace all free variables in all terms with a special symbol
`v{#sort}()`, and we can we can make an undirected multigraph where
all of these are nodes, and equations are edges. We also
add edges between nodes if we can make them equal. Then we only need to check
that the connected components make sens separately.

If our equations look like this:
```
e1: a+b = a ~> []+b
e2: a+b = b ~> a+[]
```
then the nodes of the graph would be
```
v1: v{#sort}()+v{#sort}()
v2: v{#sort}() ~> []+v{#sort}()
v3: v{#sort}() ~> v{#sort}()+[]
```
and we would have these edges:
```
v1---e1---v2
v1---e2---v3
```

This is not intended to be a design doc about how we would check for
unwanted inferences, but one can see that, e.g., if we would have
two nodes with constructors at the top in the same connected component,
then we might need to worry that we get contradictions, and we can check all
the paths between the said nodes to see if they are, indeed, reachable. It's
also easy to see that conditions do not change this model much if they are
well-behaved (e.g. we shouldn't replace equation subterms that contain
non-constructors with variables and `v=subterm` predicates).
It looks like we can also do a bit more work and also handle subterms
with non-constructors.

### Using rewriting rules with "changed" bit.

```
(a+b,x) => (a,0) ~> ([]+b,x)     if a is not a value
(a+b,x) => (b,0) ~> (a+[],x)     if a is not a value
(a, 1) ~> ([]+b, x) => (a+b, 1)
(b, 1) ~> (a+[], x) => (a+b, 1)
(a+b, x) => (a +Int b, 1)        if a and b are values
```

These rely on non-values being things that can always be evaluated.

Other than that, note that we allow decomposing an expression in any way
possible, as long as we are not extracting values, while we allow
recomposing it only if something changed. Any time we do a non heating/cooling
rewrite, we mark the term as "changed".

From a start expression, we can always extract the expression that we want to
evaluate first at the top of the evaluation stack. After evaluating it, its
"changed" bit becomes `1`, which allows us to repack the expression back,
repeating the extraction as needed.

Only extracting non-values ensures that we don't get stuck with an expression
that we can't evaluate at the top of the stack. Allowing expression repacking
only when something changed prevents rewrite cycles.

The main problem is that we're not using the original semantics, we're using
something a bit different, and we need to prove their equivalence.
