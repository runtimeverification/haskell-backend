And-Not-Exists Simplification
======================

Background
----------

Terms containing `not` show up naturally in various contexts. Examples include
`owise` clauses and configuration left-overs when applying rewriting rules in
proofs.

Owise clauses, described in 2018-09-03-Owise-encoding.md,
are solved naturally by applying the substitution resulting from matching and
simplifying.

The configuration left-overs, described in
`docs/2018-11-08-One-Path-Reachability-Proofs.md`, are not handled currently.
Their format looks something like
```
Φ(X) ∧ (¬ ∃ Z. α(Z))
```
where `Φ(X)` is the term that we attempted to rewrite and `α(Z)` is the
LHS term of a rewrite rule we managed to apply.

Other terms containing `not` are also not handled currently.

Problem/Questions
-----------------

We could implement generic handling for simplifying `not` terms based on
constructors, but a `not` would be expanded to an `or` of a very large list
of terms, which would need to be simplified. On the other hand, this should
solve the `not` evaluation once and for all.

Example:

If `C1(a, b)`, `C2(a)` and `C3(a, b, c)` are the constructors of a certain sort,
then
```
¬C1(phi, psi) =
    C2(T)
    ∨ C3(T, T, T)
    ∨ C1(phi, ¬psi)
    ∨ C1(¬phi, T)
```

We could also implement specific handling for the configuration left-overs,
leaving the generic solution for later. This would be much simpler and faster,
but would not solve the general problem.


Decision: Implement what's needed for configuration left-overs
--------------------------------------------------------------

We will implement particular handling for now, as described in
`docs/2018-11-08-Configuration-Splitting-Simplification.md`.

Reasoning
---------

For performance reasons, we would need to implement specific handling anyway.
The generic handling part may or may not be needed in the future. It seems
that the only reason for implementing generic handling first is to reduce the
development time in the short term, and that would happen only if we actually
need to solve both in the short term.

