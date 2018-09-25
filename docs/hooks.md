# Hooks

The builtin domains are listed below, categorized by sort.
Each sort and symbol is described and an example hooked declaration is given.
Note that some domains depend on others being defined!

## BOOL

No dependencies.

### BOOL.Bool

The builtin Boolean sort:

~~~
    hooked-sort Bool{}
        [hook{}("BOOL.Bool")]
~~~

Two domain values are recognized,

~~~
    \dv{Bool{}}("true")  // Boolean true
    \dv{Bool{}}("false")  // Boolean false
~~~

### BOOL.or

Logical OR: `\dv{Bool{}}("true")` if either operand is `\dv{Bool{}}("true")`, or
`\dv{Bool{}}("false")` otherwise.

~~~
    hooked-symbol or{}(Bool{}, Bool{}) : Bool{}
        [hook{}("BOOL.or")]
~~~

### BOOL.and

Logical AND: `\dv{Bool{}}("true")` if both operands are `\dv{Bool{}}("true")`,
or `\dv{Bool{}}("false")` otherwise.

~~~
    hooked-symbol and{}(Bool{}, Bool{}) : Bool{}
        [hook{}("BOOL.and")]
~~~

### BOOL.xor

Logical XOR: `\dv{Bool{}}("true")` if exactly one operand is
`\dv{Bool{}}("true")`, or `\dv{Bool{}}("false")` otherwise.

~~~
    hooked-symbol xor{}(Bool{}, Bool{}) : Bool{}
        [hook{}("BOOL.xor")]
~~~

### BOOL.eq

`\dv{Bool{}}("true")` if the operands are equal, or `\dv{Bool{}}("false")`
otherwise.

~~~
    hooked-symbol eq{}(Bool{}, Bool{}) : Bool{}
        [hook{}("BOOL.eq")]
~~~

### BOOL.ne

`\dv{Bool{}}("true")` if the operands are *not* equal, or `\dv{Bool{}}("false")`
otherwise.

~~~
    hooked-symbol ne{}(Bool{}, Bool{}) : Bool{}
        [hook{}("BOOL.ne")]
~~~

### BOOL.not

Logical negation: `\dv{Bool{}}("true")` when its argument is
`\dv{Bool{}}("false")` and vice versa.

~~~
    hooked-symbol not{}(Bool{}, Bool{}) : Bool{}
        [hook{}("BOOL.not")
~~~

### BOOL.implies

Logical implication.

~~~
    hooked-symbol implies{}(Bool{}, Bool{}) : Bool{}
        [hook{}("BOOL.implies")]
~~~

## MAP

Depends on `BOOL`.

The sorts of keys and values are arbitrary, but must be consistent between symbol
declarations. The sort consistency of hooked symbols is *not* checked. The key
and value sorts are referred to as `Key{}` and `Value{}` respectively below.

### MAP.Map

The builtin sort of key-value maps.

~~~
    hooked-sort Map{}
        [hook{}("MAP.Map")]
~~~

### MAP.unit

The empty map (containing no keys).

~~~
    hooked-symbol unit{}() : Map{}
        [hook{}("MAP.unit")]
~~~

### MAP.element

A map with one association, `key |-> value`.

~~~
    hooked-symbol element{}(Key{}, Value{}) : Map{}
        [hook{}("MAP.element")]
~~~

### MAP.concat

Combine two maps so that an association `key |-> value` is in the result if it
is in either operand. The result is `\bottom{}()` if the maps have any keys in
common.

~~~
    hooked-symbol concat{}(Map{}, Map{}) : Map{}
        [hook{}("MAP.concat")]
~~~

### MAP.update

Insert the association `key |-> value` into the map. If the key is already
present, replace the associated value with the new value provided.

~~~
    hooked-symbol update{}(Map{}, Key{}, Value{}) : Map{}
        [hook{}("MAP.update")]
~~~

### MAP.lookup

If the given key is in the map, the result is the associated value; otherwise,
the result is `\bottom{}()`.

~~~
    hooked-symbol lookup{}(Map{}, Key{}) : Value{}
        [hook{}("MAP.lookup")]
~~~

### MAP.in_keys

If the given key is in the map, the result is `\dv{Bool{}}("true")`; otherwise
the result is `\dv{Bool{}}("false")`.

~~~
    hooked-symbol inKeys{}(Map{}, Key{}) : Bool{}
        [hook{}("MAP.in_keys")]
~~~
