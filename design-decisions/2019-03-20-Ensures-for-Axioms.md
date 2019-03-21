Ensures checks
==============

Background
----------

A rewrite axiom, lemma or claim has the form
`left ∧ requires ⇒ right ∧ ensures`, where `left` and `right` are (usually)
terms, and `requires` and `ensures` are predicates. The right hand side of `⇒`
could add new variables, which are quantified existentially.

Examples that use ensure clauses could include:

Axiom:
```
random(a,b) ∧ (a ≤ b) ⇒ ∃ m . m ∧ (m ≥ a ∧ m ≤ b)
```

Claim:
```
If (a < b) then b else a ⇒ ∃ r . r ∧ ((a ≤ b ∧ r=b) ∨ (b ≤ a ∧ r=a))
```

Note that we do need ensure clauses for claims.

Questions
---------

Should we allow ensure clauses in axioms?

It is not at all obvious that we actually need them. Also, given that it is very easy to
make mistakes when writing them, should we try to detect errors?

As an example, the following axiom infers that `a ≤ b` out of thin air:
```
random(a,b) ⇒ ∃ m . m ∧ (m ≥ a ∧ m ≤ b)
```


Decision: Postpone allowing them
--------------------------------

We should show an error when encountering rewrite axioms with ensures. When
needed, we should implement the decision below. We should only allow
ensures axioms that use existential quantifiers if we don't have concrete
examples without quantifiers.

Decision: Check ensure validity
-------------------------------

We should have a flag `--rewrite-axiom-check` with three possible values:
`None`, `BestEffort` and `Strict`. We should check the
`⌈left⌉ ∧ requires ∧ ¬ensures` expression from the section below like this:

1. `None`: no checks.
1. `BestEffort`: check whether it is `⊥`, or the SMT gives up on checking it,
   fail otherwise.
1. `Strict`: check whether it is `⊥`, fail otherwise.

Reasoning
---------

Let us take a `left ∧ requires ⇒ right ∧ ensures` formula (no quantification
for now). This is equivalent to:
```
left ∧ requires ⇒ right ∧ ensures
left ∧ requires → • right ∧ ensures  -- expand ⇒
left ∧ requires → ensures ∧ • right  -- predicates can move out of •
(left ∧ requires → ensures)          -- a → b ∧ c iff (a → b) ∧ (a → c)
    ∧ (left ∧ requires → • right)
```
Now, note that this is an axiom, so the entire expression must be a
`⊤` predicate. This means that both `left ∧ requires → • right` and
`left ∧ requires → ensures` are `⊤` predicates.

But `ensures` is a predicate.
1. If `ensures` is `⊥`, then `left ∧ requires` must be `⊥`, which means that either
   `left` is `⊥` or `requires` is `⊥`, which means that either `⌈left⌉` is `⊥`  or `requires` is `⊥`
1. If `ensures` is `⊤`, then the right hand side of the implication does not
   matter.

So we should be able to replace that part of the axiom with:
```
⌈left⌉ ∧ requires → ensures
```
Which is equivalent to
```
¬ (⌈left⌉ ∧ requires ∧ ¬ensures)
```
Which we can try to validate, or we can try to see whether
`⌈left⌉ ∧ requires ∧ ¬ensures` is always `⊥`, i.e. whether it is unsatisfiable.

Now, let us take an axiom with a quantified right hand side,
`left ∧ requires ⇒ ∃ Z . right ∧ ensures`. Then this is equivalent to:
```
left ∧ requires ⇒ ∃ Z . right ∧ ensures
left ∧ requires → • ∃ Z . right ∧ ensures  -- expand ⇒
left ∧ requires → ∃ Z . • right ∧ ensures  -- ∃ commutes with •
∃ Z . left ∧ requires → • right ∧ ensures  -- ∃ commutes with ∨ and →
∃ Z . ( (left ∧ requires → • right)        -- a → b ∧ c iff (a → b) ∧ (a → c)
      ∧ (left ∧ requires → ensures)
      )
```

But note that, as above, `ensures` is a predicate, and one of the following
must happen:
1. The entire expression inside `∃ Z` is `⊥`
1. `ensures` is `⊤`
1. `left` is `⊥`
1. `requires` is `⊥`

But there must be at least one `Z` for which the entire expression inside `∃ Z`
is not `⊥`, so there must be at least one `Z` for which
`ensures` is `⊤`, `left` is `⊥`, or `requires` is `⊥`, which means that there
is one `Z` for which, as above, `¬(⌈left⌉ ∧ requires ∧ ¬ensures)`,
which means that:
```
∃ Z . ¬ (⌈left⌉ ∧ requires ∧ ¬ensures)
¬ ∀ Z . (⌈left⌉ ∧ requires ∧ ¬ensures)  -- ∃ Z . ¬ φ iff ¬ ∀ Z . φ
```
But this means that `∀ Z . (⌈left⌉ ∧ requires ∧ ¬ensures)` is `⊥`, which means
that, as above, `(⌈left⌉ ∧ requires ∧ ¬ensures)` is `⊥`.
