# Sorts of Kore implicits

This document describes the sort signatures of the Kore implicits.

## Connectives

```
\top{S}() : S
\bottom{S}() : S
```

```
\not{S}(S) : S
```

```
\and{S}(S, S) : S
\or{S}(S, S) : S
\implies{S}(S, S) : S
\iff{S}(S, S) : S
```

## Quantifiers

```
\exists{S}(x:T, S)
\forall{S}(x:T, S)
```

## Fixpoints

```
\mu{}(@X:S, S) : S
\nu{}(@X:S, S) : S
```

## Predicates

```
\ceil{S, R}(S) : R
\floor{S, R}(S) : R
```

```
\equals{S, R}(S, S) : R
\in{S, R}(S, S) : R
```

## Rewriting

```
\next{S}(S) : S
```

```
\rewrites{S}(S, S) : S
```

## Domain values

```
\dv{S}(#String) : S
```
