# Simple tests related to (internalised) Map and Set

The definition for these tests imports `MAP` and `SET`, and defines a custom
`Collection` sort as a supersort of `Set`, as well as a `State ( Collection, Int )`.

The only rule in the definition counts down from the `Int` in the `State`,
while adding the numbers it counts down from to the `Collection`.

* `state-from-12.execute` request: starts from `State ( .Set, 12 )`
   - Expected response: `State( {1..12}, 0}`
* `state-map-lookup.simplify` request for `{ 1 -> 111, 2 -> AVARIABLE }[1]`
   - Expected response: `111` (as a `KItem`)
* `state-map-lookupOrDefault.simplify` request for `{ 1 -> 111, 2 -> AVARIABLE }[0] orDefault 0`
   - Expected response: `0` (as a `KItem`)
* `state-map-in_keys-true.simplify` request for `1 in_keys { 1 -> 111, 2 -> AVARIABLE }`
   - Expected response: `true`
* `state-map-in_keys-false.simplify` request for `0 in_keys { 1 -> 111, 2 -> AVARIABLE }`
   - Expected response: `false`
* `state-map-in_keys-undetermined.simplify` request for `0 in_keys AMAP`
   - Expected response: `0 in_keys AMAP` (unsimplified)
