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

## INT

Depends on `BOOL`.

### INT.Int

The builtin sort of arbitrary-precision integers.

~~~
    hooked-sort Int{}
        [hook{}("INT.Int")]
~~~

Valid domain values are a string of decimal digits, optionally preceeded by a
sign.

~~~
    \dv{Int{}}("256")  // positive 256, sign omitted
    \dv{Int{}}("-1024")  // negative 1024
    \dv{Int{}}("+3")  // positive 3
~~~

### INT.gt

Comparison: is the first argument greater than the second?

~~~
    hooked-symbol gt{}(Int{}, Int{}) : Bool{}
        [hook{}("INT.gt")]
~~~

### INT.ge

Comparison: is the first argument greater than or equal to the second?

~~~
    hooked-symbol ge{}(Int{}, Int{}) : Bool{}
        [hook{}("INT.ge")]
~~~

### INT.eq

Comparison: is the first argument equal to the second?

~~~
    hooked-symbol eq{}(Int{}, Int{}) : Bool{}
        [hook{}("INT.eq")]
~~~

### INT.le

Comparison: is the first argument less than or equal to the second?

~~~
    hooked-symbol le{}(Int{}, Int{}) : Bool{}
        [hook{}("INT.le")]
~~~

### INT.lt

Comparison: is the first argument less than the second?

~~~
    hooked-symbol lt{}(Int{}, Int{}) : Bool{}
        [hook{}("INT.lt")]
~~~

### INT.ne

Comparison: is the first argument inequal to the second?

~~~
    hooked-symbol ne{}(Int{}, Int{}) : Bool{}
        [hook{}("INT.ne")]
~~~

### INT.add

The sum of the arguments.

~~~
    hooked-symbol add{}(Int{}, Int{}) : Int{}
        [hook{}("INT.add")]
~~~

### INT.sub

The difference of the arguments (the first less the second).

~~~
    hooked-symbol sub{}(Int{}, Int{}) : Int{}
        [hook{}("INT.sub")]
~~~

### INT.mul

The product of the arguments.

~~~
    hooked-symbol mul{}(Int{}, Int{}) : Int{}
        [hook{}("INT.mul")]
~~~

### INT.abs

The absolute value of the argument.

~~~
    hooked-symbol abs{}(Int{}) : Int{}
        [hook{}("INT.abs")]
~~~

### INT.tdiv

Quotient of the first argument divided by the second (truncated toward zero).
The result is `bottom{}()` if the second argument is zero.

~~~
    hooked-symbol tdiv{}(Int{}, Int{}) : Int{}
        [hook{}("INT.tdiv")]
~~~

### INT.tmod

Remainder of the first argument divided by the second (truncated toward zero).
The result is `bottom{}()` if the second argument is zero.

~~~
    hooked-symbol tmod{}(Int{}, Int{}) : Int{}
        [hook{}("INT.tmod")]
~~~

### INT.and

Bitwise and of the arguments.

~~~
    hooked-symbol and{}(Int{}, Int{}) : Int{}
        [hook{}("INT.and")]
~~~

### INT.or

Bitwise or of the arguments.

~~~
    hooked-symbol or{}(Int{}, Int{}) : Int{}
        [hook{}("INT.or")]
~~~

### INT.xor

Bitwise exclusive or of the arguments.

~~~
    hooked-symbol xor{}(Int{}, Int{}) : Int{}
        [hook{}("INT.xor")]
~~~

### INT.not

Bitwise complement of the argument.

~~~
    hooked-symbol not{}(Int{}) : Int{}
        [hook{}("INT.not")]
~~~

### INT.shl

Shift the bits of the first argument to the left. The second argument specifies
how many bits to shift by, and will be truncated to the least-significant
Haskell Int. The second argument can be negative, in which case the first
argument will be shifted right.

~~~
    hooked-symbol shl{}(Int{}, Int{}) : Int{}
        [hook{}("INT.shl")]
~~~

### INT.shr

Shift the bits of the first argument to the right. The second argument specifies
how many bits to shift by, and will be truncated to the least-significant
Haskell Int. The second argument can be negative, in which case the first
argument will be shifted left.

~~~
    hooked-symbol shr{}(Int{}, Int{}) : Int{}
        [hook{}("INT.shr")]
~~~

### INT.pow

The first argument raised to the power of the second argument. The result is
`bottom{}()` if the second argument is negative.

~~~
    hooked-symbol pow{}(Int{}, Int{}) : Int{}
        [hook{}("INT.pow")]
~~~

### INT.powmod

The first argument raised to the power of the second argument, but performed
modulo the third argument. The result is `\bottom{}()` if either
- The second argument is zero, or
- The second argument is negative and the first and third arguments are not
  coprime

~~~
    hooked-symbol powmod{}(Int{}, Int{}, Int{}) : Int{}
        [hook{}("INT.powmod")]
~~~

### INT.log2

The base 2 logarithm of the argument. The result is `bottom{}()` if the second
argument is not positive.

~~~
    hooked-symbol log2{}(Int{}) : Int{}
        [hook{}("INT.log2")]
~~~

## STRING

Depends on `BOOL`.

### STRING.String

The builtin String sort:

~~~
    hooked-sort String{}
        [hook{}("STRING.String")]
~~~

Valid domain values are strings.

~~~
    \dv{String{}}("string")
~~~

### STRING.lt

Comparison: is the first argument less than the second?

~~~
    hooked-symbol lt{}(String{}, String{}) : Bool{}
        [hook{}("STRING.lt")]
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

## LIST

Depends on `INT`.

The sort of list elements is arbitrary, but must be consistent between symbol
declarations. The sort consistency of hooked symbols is *not* checked. The
element sort is referred to as `Elem{}` below.

### LIST.List

The builtin sort of associative lists.

~~~
    hooked-sort List{}
        [hook{}("LIST.List")]
~~~

### LIST.unit

The empty list.

~~~
    hooked-symbol unit{}() : List{}
        [hook{}("LIST.unit")]
~~~

### LIST.element

The singleton list.

~~~
    hooked-symbol element{}(Elem{}) : List{}
        [hook{}("LIST.element")]
~~~

### LIST.concat

Concatenate both arguments.

~~~
    hooked-symbol concat{}(List{}, List{}) : List{}
        [hook{}("LIST.concat")]
~~~

### LIST.get

Get an element from the list by index. Positive indices count from the beginning
of the list and negative indices count from the end. The first element is
`\dv{Int{}}("0")` and the last element is `\dv{Int{}}("-1")`. The result is
`\bottom{}()` if the index is out-of-bounds.

~~~
    hooked-symbol get{}(List{}, Int{}) : Elem{}
        [hook{}("LIST.concat")]
~~~

## SET

Depends on `BOOL`.

The sort of set elements is arbitrary, but must be consistent between symbol
declarations. The sort consistency of hooked symbols is *not* checked. The
element sort is referred to as `Elem{}` below.

### SET.Set

The builtin sort of sets.

~~~
    hooked-sort Set{}
        [hook{}("SET.Set")]
~~~

### SET.unit

The empty set.

~~~
    hooked-symbol unit{}() : Set{}
        [hook{}("SET.unit")]
~~~

### SET.element

The singleton set.

~~~
    hooked-symbol element{}(Elem{}) : Set{}
        [hook{}("SET.element")]
~~~

### SET.concat

The union of both arguments.

~~~
    hooked-symbol concat{}(Set{}, Set{}) : Set{}
        [hook{}("SET.concat")]
~~~

### SET.in

Is the element a member of the given set?

~~~
    hooked-symbol in{}(Elem{}, Set{}) : Bool{}
        [hook{}("SET.in")]
~~~

## KEQUAL

Depends on `BOOL`.

The sorts on which equality is tested are referred to as `Item`.

### KEQUAL.eq

Comparison: is the first argument equal to the second?

~~~
    hooked-symbol eq{}(Item{}, Item{}) : Bool{}
        [hook{}("KEQUAL.eq")]
~~~


### KEQUAL.neq

Comparison: is the first argument inequal to the second?

~~~
    hooked-symbol neq{}(Item{}, Item{}) : Bool{}
        [hook{}("KEQUAL.neq")]
~~~

### KEQUAL.ite

If-then-else: if condition then something, else something else.

~~~
    hooked-symbol neq{}(Bool{}, Item{}, Item{}) : Item{}
        [hook{}("KEQUAL.ite")]
~~~
