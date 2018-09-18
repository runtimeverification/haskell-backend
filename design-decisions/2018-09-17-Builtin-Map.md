Builtin Maps
============

Background
----------

K provides a builtin `Map` sort representing partial maps on sort `K`.
Here "partial" means that some keys may not be associated with any value.
KEVM relies on concrete operations only, but we will eventually need to support
symbolic operations.

Operations
----------

The builtin `Map` domain should support operations equivalent to:

```
module MAP
    sort Map{} []

    // unit: The empty map (no keys).
    symbol unit{}() : Map{} []

    // element(key, value): A map from one key to one value.
    symbol element{}(K{}, K{}) : Map{} []

    // concat(map1, map2): Combine both maps so that a key is in the result if
    // it is in either operand.
    symbol concat{}(Map{}, Map{}) : Map{} []

    // update(map, key, value): Update the map so that key refers to value.
    symbol update{}(Map{}, K{}, K{}) : Map{} []

    // lookup(map, key): Lookup key in map and return the associated value.
    // Return \bottom if the key is missing.
    symbol lookup{}(Map{}, K{}) : K{} []

    // inKeys(map, key): Is key in map?
    symbol inKeys{}(Map{}, K{}) : Bool{} []
endmodule
```

Questions:

- What does `update` do if the key is missing from the map?
- What does `concat` do if the key is present in both maps?

Concrete operations
-------------------

Existing semantics, particularly KEVM, rely on concrete map operations.
Therefore, we may assume all keys are concrete, i.e. contain no variables.
In case a key is symbolic, the existing backends treat it as a concrete pattern
and perform lookup by exact structural equality of patterns.
For the immediate purpose of supporting KEVM, we may do the same:
perform key lookup by exact structural equality between patterns.

Symbolic operations
-------------------

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
