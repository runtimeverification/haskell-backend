Unification with equations
==========================

Summary
-------

Proposal: Write k/kore axioms/theorems allowing us both to solve unification
in a principled way without changing the backend for each of these cases,
and to easily generate proofs if/when that will be desirable.

Background
----------

The most general unifier of `φ` and `ψ` is `⌈φ∧ψ⌉`

There are some unification cases that are easy to solve, e.g. if `C` is a
constructor (actually, it only needs to be injective), then
```
⌈C(φ₁, …, φ_n) ∧ C(ψ₁, …, ψ_n)⌉=⌈φ₁∧ψ₁⌉∧…∧⌈φ_n∧ψ_n⌉
```

However, if `f` and `g` are random symbols, without any properties, then
`⌈f(φ₁, …, φ_n) ∧ g(ψ₁, …, ψ_m)⌉` cannot be reduced to a nicer form.

If `f` is, say, an associative binary operation with neutral element (i.e. the
concatenation for a list), then we have a reasonable intuition about how to
unify it, but I don’t know of any written text about that.

Problem
-------

We are trying to extend unification to sorts that do not have constructors, but
which have something resembling constructors. An example is a list, which has:
`unit` - the empty list.
`elem` - takes an element of a different sort and produces a single element list.
`concat` - concatenates two lists.
Heating and cooling could be another example.

Proposed Solution
-----------------

The first attempt to solve this would be to define some sort of
no-junk/no-confusion axiom
for that sort (e.g. any list can be built with `unit`, `elem` and `concat`),
and then expand the two terms in all possible ways using the available
equations, then match the two terms at the top as long as we stay within
the same sort, then use unification for the remainders.

However, this has a few problems. First, there is no way of proving that
this is the most general unifier, i.e. there is no way of showing that we
truly expanded the term in all possible ways. Second, this would be really
inefficient. Also, the no-confusion axioms might be hard to write.

### Actual proposal

The second attempt, however, would be to define some unification axioms (I
think that they are, indeed, axioms, but they could be theorems if we find
a way to infer them), specifying how to solve certain unification cases
in a way that can be used almost directly by the Haskell backend (some
changes needed).

These axioms would allow us to reduce the hard to handle
unification cases to unambiguous ones (e.g. reduce AC unification to
constructor-based unification).

See the use-cases below for examples and explanations.

We could write these in a way that we don't duplicate unification cases.
Then we could apply these as simplification axioms, defining our unification
strategy in k. When we need performance, we could implement the ones that are
used more frequently in Haskell.

Or, if that ever becomes desirable (e.g. if we want it to make proof
certificates easier to generate), we could give up on performance and define
all simplification cases as axioms/theorems.

Also, we should probably use set variables, to avoid the large number of
checks needed when working with normal variables (though, of course, we
need to make sure that the axioms still hold).

Use-case: lists
---------------

For lists, we could have the following axioms
```
⌈elem(x)∧unit⌉ = ⊥
⌈elem(x)∧elem(y)⌉ = ⌈x∧y⌉
⌈concat(l₁,l₂) ∧ unit⌉ = ⌈l₁∧unit⌉ ∧ ⌈l₂∧unit⌉
⌈concat(elem(x),l₁) ∧ concat(elem(z), l₂)⌉ = ⌈x∧z⌉ ∧ ⌈l₁∧l₂⌉
```
This is missing some axioms (e.g. the ones unifying at the end of the list,
or splitting the list), but it looks like these, together with the usual list
axioms and the `and` commutativity axioms could be enough to solve list
unification.

Note that applying these axioms allows us to reduce complex expressions to
simpler ones, without worrying about how many terms are equivalent to the
one we have: we just have to bring the term in one of the forms required for
one of these axioms, then we apply the axiom and that’s it.

As an example, say we need to unify `concat(concat(elem(φ₁), elem(φ₂)), φ₃)`
with `concat(concat(unit, elem(ψ₁)), concat(elem(ψ₂), ψ₃))`. We first use
the list axioms to rewrite the first term as
`concat(elem(φ₁), concat(elem(φ₂), φ₃))`, the second one as
`concat(elem(ψ₁), concat(elem(ψ₂), ψ₃))`, then we apply the
`⌈concat(elem(x),l₁) ∧ concat(elem(z),l₂)⌉ = ⌈x∧z⌉ ∧ ⌈l₁∧l₂⌉` axiom repeatedly
to compute
```
⌈ concat(elem(φ₁), concat(elem(φ₂), φ₃))
∧ concat(elem(ψ₁), concat(elem(ψ₂), ψ₃)) ⌉
    = ⌈φ₁∧ψ₁⌉ ∧ ⌈concat(elem(φ₂), φ₃) ∧ concat(elem(ψ₂), ψ₃)⌉
    = ⌈φ₁∧ψ₁⌉ ∧ ⌈φ₂∧ψ₂⌉ ∧ ⌈φ₃∧ψ₃⌉
```

Use-case: multi-sets
--------------------

These are associative, commutative, with neutral element.

Let us try to define the axioms for multi-set lookup through unification, i.e.
for unifying `concat(elem(x), s)` with a multi-set. Assuming that our terms are
normalized (elems moved to the left, concats represented as
`concat(a, concat(b, concat(...)))`), then the following axioms should be
enough:

```
⌈concat(s₁,s₂) ∧ unit⌉ = ⌈s₁∧unit⌉ ∧ ⌈s₂∧unit⌉
⌈concat(elem(x), s) ∧ elem(a)⌉ = ⌈x∧a⌉ ∧ ⌈s∧unit⌉
⌈concat(elem(x), s₁) ∧ concat(elem(a), s₂)⌉
    = ⌈x∧a⌉ ∧ ⌈s₁∧s₂⌉
      ∨ ∃ s₃ . ⌈concat(elem(x),s₃)∧s₂⌉ ∧ ⌈s₁∧concat(elem(a),s₃)⌉
```

As an example, the left-to-right implication for the equality above can be
shown like this (predicate equality is equivalence):
```
x\and⌈x∧a⌉ = a\and⌈x∧a⌉
s₁\and⌈s₁∧s₂⌉ = s₂\and⌈s₁∧s₂⌉

concat(elem(x), s₁)\and⌈x∧a⌉\and⌈s₁∧s₂⌉
    = concat(elem(x\and⌈x∧a⌉), s₁\and⌈s₁∧s₂⌉)\and⌈x∧a⌉\and⌈s₁∧s₂⌉
    = concat(elem(a\and⌈x∧a⌉), s₂\and⌈s₁∧s₂⌉)\and⌈x∧a⌉\and⌈s₁∧s₂⌉
    = concat(elem(a), s₂)\and⌈x∧a⌉\and⌈s₁∧s₂⌉
```
therefore `⌈x∧a⌉\and⌈s₁∧s₂⌉` is a unifier of `concat(elem(x), s₁)` and
`concat(elem(a), s₂)`.
Similarly, we have
```
concat(elem(x),s₃)\and⌈concat(elem(x),s₃)∧s₂⌉=s₂\and⌈concat(elem(x),s₃)∧s₂⌉
therefore
concat(elem(a), concat(elem(x),s₃))\and⌈concat(elem(x),s₃)∧s₂⌉
    =concat(elem(a),s₂)\and⌈concat(elem(x),s₃)∧s₂⌉

also,
s₁∧⌈s₁∧concat(elem(a),s₃)⌉=concat(elem(a),s₃)∧⌈s₁∧concat(elem(a),s₃)⌉
therefore
concat(elem(x), s₁)∧⌈s₁∧concat(elem(a),s₃)⌉
    = concat(elem(x), concat(elem(a),s₃))∧⌈s₁∧concat(elem(a),s₃)⌉

but this means that we have
concat(elem(x), s₁)\and⌈concat(elem(x),s₃)∧s₂⌉∧⌈s₁∧concat(elem(a),s₃)⌉
    = concat(elem(x), concat(elem(a),s₃))
      \and ⌈concat(elem(x),s₃)∧s₂⌉ ∧ ⌈s₁∧concat(elem(a),s₃)⌉
    = concat(elem(a),s₃)\and⌈concat(elem(x),s₃)∧s₂⌉∧⌈s₁∧concat(elem(a),s₃)⌉
```
therefore `⌈concat(elem(x),s₃)∧s₂⌉∧⌈s₁∧concat(elem(a),s₃)⌉` is a unifier of
`concat(elem(x), s₁)` and `concat(elem(a), s₂)`, which means that the RHS of the
equality is included in the LHS, since that is the most general unifier of the
two.

Use-case: sets
--------------

These are associative, commutative, idempotent, with neutral element.

Let us try to define the axioms for unifying `concat(elem(x), s)` with a set.
As above, we are assuming that our terms are normalized (elems moved to the
left, concats represented as `concat(a, concat(b, concat(...)))`, identical
elements removed). The following axioms should be enough:

```
⌈concat(s₁,s₂) ∧ unit⌉ = ⌈s₁∧unit⌉ ∧ ⌈s₂∧unit⌉
⌈concat(elem(x), s) ∧ elem(a)⌉ = ⌈x∧a⌉ ∧ (⌈s∧unit⌉ ∨ ⌈s∧a⌉)
⌈concat(elem(x), s₁) ∧ concat(elem(a), s₂)⌉
    = ⌈x∧a⌉ ∧ (⌈s₁∧s₂⌉ ∨ ⌈s₁∧ concat(elem(a), s₂)⌉)
      ∨
      (¬⌈x∧a⌉ ∧ ∃ s₃ . ⌈concat(elem(x),s₃)∧s₂⌉ ∧ ⌈s₁∧concat(elem(a),s₃)⌉)
```

Use case: heating and cooling
-----------------------------

Let’s say that we want to do heating and cooling using equations instead of
rewriting rules. We might have
```
(a + b) = a ~> ([] + b)
(a + b) = b ~> (a + [])
```
as equations.
Now, if we want to apply
```
x + y ~> z ⇒ x +Int y ~> z    if isValue(x) ∧ isValue(y)
```
to something like
```
((1 + 2) + (3 + 4))
```
we need to unify `x + y ~> z` with `((1 + 2) + (3 + 4))`. While we could expand
the expression in all possible ways and apply matching for the top `~>`, we
could do this in a more principled way if we had the following axiom:
```
⌈x~>y ∧ (a+b)⌉ =
    (⌈x ∧ (a+b)⌉ ∧ ⌈y ∧ unit⌉)
    ∨ ∃ d . (⌈x~>d ∧ a⌉ ∧ ⌈y ∧ (d~>[]+b)⌉)
    ∨ ∃ d . (⌈x~>d ∧ b⌉ ∧ ⌈y ∧ (d~>a+[])⌉)
  if isKItem(x)
```

This would give us a clear way of doing unification, in which we'd be sure that
we're not missing any terms when expanding, and which would make it easy to
prove that we're doing the right thing.
