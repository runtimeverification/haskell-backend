Builtin Maps
============

Background
----------

K provides a builtin `Map` sort representing partial maps on sort `K`.
Here "partial" means that some keys may not be associated with any value.
KEVM relies on concrete operations only, but we will eventually need to support
symbolic operations.

Problem
-------

KEVM requires that the builtin `Map` domain supports operations equivalent to:

```
module MAP
    hooked-sort Map{}
        [hook{}("MAP.Map")]

    // unit:
    // The empty map (containing no keys).
    hooked-symbol unit{}() : Map{}
        [hook{}("MAP.unit")]

    // element(key, value):
    // A map from with exactly one association: ‘key |-> value’.
    hooked-symbol element{}(K{}, K{}) : Map{}
        [hook{}("MAP.element")]

    // concat(map1, map2):
    // Combine ‘map1’ and ‘map2’ so that the association ‘key |-> value’ is in
    // the result if it is in one operand. The result is ‘\bottom{}()’ if
    // ‘map1’ and ‘map2’ have any keys in common.
    hooked-symbol concat{}(Map{}, Map{}) : Map{}
        [hook{}("MAP.concat")]

    // update(map, key, value):
    // Update ‘map’ with the association ‘key |-> value’.
    // The ‘key’ may or may not be present in ‘map’.
    hooked-symbol update{}(Map{}, K{}, K{}) : Map{}
        [hook{}("MAP.update")]

    // lookup(map, key):
    // If ‘map’ contains the association ‘key |-> value’, then the result
    // is ‘value’; otherwise the result is ‘\bottom{}()’.
    hooked-symbol lookup{}(Map{}, K{}) : K{}
        [hook{}("MAP.lookup")]

    // inKeys(map, key):
    // If ‘map’ contains any association ‘key |-> _’, then the result is
    // ‘\dv{Bool{}}("true")’; otherwise the result is ‘\dv{Bool{}}("false")’.
    hooked-symbol inKeys{}(Map{}, K{}) : Bool{}
        [hook{}("MAP.in_keys")]
endmodule
```

Decision: Implement concrete operations immediately
---------------------------------------------------

Existing semantics, particularly KEVM, rely on concrete map operations.
Therefore, we may assume all keys are concrete, i.e. contain no variables.
In case a key is symbolic, the existing backends treat it as a concrete pattern
and perform lookup by exact structural equality of patterns.
For the immediate purpose of supporting KEVM, we may do the same:
perform key lookup by exact structural equality between patterns.

Decision: Defer implementing symbolic operations
------------------------------------------------

Eventually we will support both concrete and symbolic map operations.
Once we support concrete operations, we can add support for symbolic operations
by keeping symbolic constructions unevaluated, i.e. a symbolic map will be a
pattern consisting of an unevaluated symbolic operation upon a symbolic or
concrete map.
Evaluating lookups from a symbolic map will require traversing the symbolic map
pattern and attempting unification against each key.
Looking up a symbolic key will traverse the entire map and will potentially be
very expensive, so we will want to fall back to concrete lookup whenever
possible; therefore it is in our best interest to implement concrete operations
first.

There is a trade-off to make between evaluating symbolic insertion and lookup.
Either operation can be left as an unevaluated pattern.
When evaluated, the symbolic operations may generate a large disjunction of
patterns; the trade-off is _when_ the disjunction is generated.
We have tentatively decided to evaluate lookups and leave insertions unevaluated.
During a lookup, all the branches where the key does not unify can be discarded,
so there may be fewer branches to explore.
On the other hand, the result of evaluating an insertion is always the largest
possible disjunction.

Questions
---------

- How should substitution behave with respect to symbolic maps?
