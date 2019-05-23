Unification with equations
==========================

Background
----------

The most general unifier of `φ` and `ψ` is `⌈φ∧ψ⌉`

There are some unification cases that are easy to solve, e.g. if `C` is a
constructor (actually, it only needs to be injective), then
```
⌈C(φ_1, …, φ_n) ∧ C(ψ_1, …, ψ_n)⌉=⌈φ_1∧ψ_1⌉∧…∧⌈φ_n∧ψ_n⌉
```

However, if `f` and `g` are random symbols, without any properties, then
`⌈f(φ_1, …, φ_n) ∧ g(ψ_1, …, ψ_m)⌉` cannot be reduced to a nicer form.

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

Solution
--------

The first attempt to solve this would be to define some sort of
no-junk/no-confusion axiom
for that sort (e.g. any list can be built with `unit`, `elem` and `concat`),
and then expand the two terms in all possible ways using the available
equations, then match the two terms at the top as long as we stay within
the same sort, then use unification for the remainders.

However, this has a few problems. First, there is no way of proving that
this is the most general unifier, i.e. there is no way of showing that we
truly expanded the term in all possible ways. Second, this would be really
inefficient.

The second attempt, however, would be to define some unification axioms (I
think that they are, indeed, axioms, but they could be theorems if we find
a way to infer them), specifying how to solve certain unifications. As an
example, for lists, we could have
```
⌈elem(x)∧unit⌉=⊥
⌈elem(x)∧elem(y)⌉=⌈x∧y⌉
⌈concat(x,y)∧unit⌉=⌈x∧unit⌉∧⌈y∧unit⌉
⌈concat(elem(x),y)∧concat(elem(z),t)⌉=⌈x∧z⌉∧⌈y∧t⌉
```
This is missing some axioms (e.g. the ones unifying at the end of the list,
or splitting the list), but it looks like this, together with the usual list
axioms and the `and` commutativity axioms could be enough to solve list
unification.

Note that applying these axioms allows us to reduce complex expressions to
simpler ones, without worrying about how many terms are equivalent to the
one we have: we just have to bring the term in one of the forms required for
one of these axioms, then we apply the axiom and that’s it.

As an example, say we need to unify `concat(concat(elem(φ_1), elem(φ_2)), φ_3)`
with `concat(concat(unit, elem(ψ_1)), concat(elem(ψ_2), ψ_3))`. We first use
the list axioms to rewrite the first term as
`concat(elem(φ_1), concat(elem(φ_2), φ_3))`, the second one as
`concat(elem(ψ_1), concat(elem(ψ_2), ψ_3))`, then we apply the
`⌈concat(elem(x),y)∧concat(elem(z),t)⌉=⌈x∧z⌉∧⌈y∧t⌉` axiom repeatedly to compute
```
⌈ concat(elem(φ_1), concat(elem(φ_2), φ_3))
∧ concat(elem(ψ_1), concat(elem(ψ_2), ψ_3)) ⌉
    = ⌈φ_1∧ψ_1⌉∧⌈concat(elem(φ_2), φ_3)∧concat(elem(ψ_2), ψ_3)⌉
    = ⌈φ_1∧ψ_1⌉∧⌈φ_2∧ψ_2⌉∧⌈φ_3∧ψ_3⌉
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
⌈(a+b)~>c ∧ (d+e)~>f⌉ =
    (⌈a∧d⌉ ∧ ⌈b∧e⌉ ∧ ⌈c∧f⌉)
    ∨ (⌈(a+b)~>g ∧ d⌉ ∧ ⌈c ∧ (g~>[]+e~>f)⌉)
    ∨ (⌈(a+b)~>g ∧ e⌉ ∧ ⌈c ∧ (g~>d+[]~>f)⌉)
```
This would give us a clear way of doing unification, in which we'd be sure that
we're not missing any terms when expanding, and which would make it easy to
prove that we're doing the right thing.
