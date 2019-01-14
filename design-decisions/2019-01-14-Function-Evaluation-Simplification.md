Function evaluation and simplification
======================================

Background
----------

We have two types of axiom for function evaluation: function definition axioms
and simplification axioms. The former, taken together, cover all cases when a
function is defined, and they are expected to always match. The latter are
useful when they can be matched, but they are not essential.
However, currently we are not differentiating between the two axiom types.

Examples:

Function definition:
```
sgn(x) = 1 if x > 0
sgn(x) = -1 if x < 0
sgn(x) = 0 otherwise
```

Function simplification:
```
((x mod y) + (z mod y)) mod y = (x + z) mod y
```

When evaluating a function we match on the expression shape, then, when
that's different, we resolve everything else as equality constraints, e.g. when
matching the function simplification axiom above with `a mod b` we would get
`(x + z) mod b  and  a = ((x mod y) + (z mod y))` as the result.

However, that's undesirable for simplification axioms.

When simplifying normal functions we may encounter constraints like
`concat(elem(x,y),z) = map-domain-value`. Note that this uses constructor-like
symbols (`concat` and `elem`), unlike the above constraint
(`a = ((x mod y) + (z mod y))`) which uses normal functions (`+` and `mod`).

Also see `docs/2018-12-21-Function-Evaluation.md`.

Problem/Questions
-----------------

Should we add an attribute differentiating definition axioms from simplification
axioms?

Should we just change the function evaluation code to work with both types of
axioms?


Decision: Function definition attribute
---------------------------------------

Long term, we should add a function simplification attribute, since it's the
safest way to solve the problem.

Note that it may make more sense to add a function definition attributes since,
in principle, definition axioms are in `O(symbol-count)`, while we could have
any number of simplification axioms. However, in practice it would probably
be undesirable to add these attributes to the main semantics (especially
to the existing semantics), so we'll use simplification attributes.

Decision: No matching constraints with functions over axiom variables
---------------------------------------------------------------------

Constraints with normal functions (i.e. not constructors) over axiom variables
are not easily solvable and almost surely do not come from function definition
axioms. Therefore we should not attempt to apply axioms generating these
when matching since the result will probably be more complex than the input
and it does not make sense to apply a simplification axiom in order to get
something more complex.

If we have these, matching should fail, i.e. it should throw an error.

Decision: Allow matching constraints with functions without axiom variables
---------------------------------------------------------------------------

If any variables in the result have constructor-like symbols on top of them,
the constraint seems more like a function definition one than like a
simplification one, so we will allow it.

Decision: Free pass for inputs made of constructor-like stuff
-------------------------------------------------------------

We will allow matching on axiom patterns made of constructor-like symbols
regardless of how the resulting constraint looks.

Note that this is actually a subcase of
"Allow matching constraints with functions without axiom variables". However,
in the future we may want to allow only this kind of matching.
