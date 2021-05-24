# Simplifying predicates

The goals of simplification are:

1. Transform the predicate into [disjunctive normal form] (normalization).
2. Apply identities to reduce the complexity of the predicate (simplification proper).

Simplification happens recursively, upward from the bottom. Therefore, we
describe the simplification steps based on the shape of the top-most
unsimplified clause of the predicate.

## \and

### Normalization

Apply this distributive law over both arguments of `\and` until `P[n]` are all
in disjunctive normal form:

``` kore
\and(\or(P[1], P[2]), P[3]) = \or(\and(P[1], P[3]), \and(P[2], P[3]))
```

### Simplification

#### Identity

``` kore
\and(\top, P[1]) = P[1]
```

#### Annihilation

``` kore
\and(\bottom, _) = \bottom
```

#### Idempotence

``` kore
\and(P[1], P[1]) = P[1]
```

#### Affirmation

Idempotence is actually a special case of _affirmation_,

``` kore
\and(P[1], P[2]) = \and(P[1], P[2](P[1] = \top))
```

## \or

### Normalization

Assuming the children of `\or` are in disjunctive normal form, then the clause
is already normalized.

### Simplification

#### Identity

``` kore
\or(\bottom, P[1]) = P[1]
```

#### Annihilation

``` kore
\or(\top, _) = \top
```

#### Idempotence

``` kore
\or(P[1], P[1]) = P[1]
```

#### Affirmation

This one is not as useful as the rule for `\and`:

``` kore
\or(P[1], P[2]) = \not(\and(\not(P[1]), \not(P[2])))
  = \not(\and(\not(P[1]), \not(P[2](P[1] = \bottom))))
  = \or(P[1], P[2](P[1] = \bottom))
```

## \bottom

`\bottom` is already in disjunctive normal form.

## \top

`\top` is already in disjunctive normal form.

## \not

### Normalization

``` kore
\not(\or(P[1], P[2])) = \and(\not(P[1]), \not(P[2]))
```

### Simplification

#### \top

``` kore
\not(\top) = \bottom
```

#### \bottom

``` kore
\not(\bottom) = \top
```

#### \not

``` kore
\not(\not(P)) = P
```

## \implies

### Normalization

``` kore
normalize(\implies(L, R)) = \or(normalize(\not(L)), normalize(\and(L, R)))
```

Note: We carry `L` through to the right-hand side because this maximizes the
information content of the second clause of the disjunction.

### Simplification

#### \top

``` kore
\implies(\top, P) = P
```

#### \bottom
``` kore
\implies(\bottom, _) = \top
```

## \iff

### Normalization

`\iff` is desugared to `\implies`.

``` kore
normalize(\iff(L, R)) =
  \or(normalize(\and(\not(L), \not(R))), normalize(\and(L, R)))
```

### Simplification

#### \top

``` kore
\iff(\top, P) = \iff(P, \top) = P
```

#### \bottom

``` kore
\iff(\bottom, P) = \iff(P, \bottom) = \not(P)
```

[disjunctive normal form]: https://en.wikipedia.org/wiki/Disjunctive_normal_form