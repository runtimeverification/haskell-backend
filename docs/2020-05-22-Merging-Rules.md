Combining multiple rules in a single equivalent rule
====================================================


Introduction
------------

Rule application can benefit from indexing of rules and using efficient
data-structures to decide faster which rule can be applied on a given
configuration.

This document attempts to justify this approach from a provability point of
view, to ensure that the indexing algorithms are provably sound.

### Background

K rules, are of the form

    rule l => r requires c

where, in general, l is a constructor-based term
(modulo axioms: may contain Ac constructors, overloadable constructors)

When translated into matching logic, they are of the form

    axiom l ∧ c → • r

Where • is the next operator, meaning that there is a possible transition
from l (satisfying c) to r.

Approach
--------

We will only discuss here combining two rules, but it should be clear
that this easily extends to any finite number of rules.

### FOL Interlude

The following is provable using FOL reasoning:

```coq
Theorem combine
  (p1 q1 p2 q2 : var → Prop)
  (i j : nat)
  (Hnij : i <> j)
  : (∀ x, p1  x → q1 x) ∧ (∀ y, p2 y → q2 y) 
    ↔ ∀ (c : nat) x y,
        (c = i ∧ p1 x) ∨ (c = j ∧ p2 y)
        → (c = i ∧ q1 x) ∨ (c = j ∧ q2 y).
```

### Back to ML

Given two rules

    axiom ∀ x1 . l1 → • r1
    axiom ∀ x2 . l2 → • r2

From the theorem above, we can combine the two axiom into an equivalent one:

    axiom ∀ c x1 x2 .
        (c = 1 ∧ l1) ∨ (c = 2 ∧ l2) →
        (c = 1 ∧ • r1) ∨ (c = 2 ∧ • r2)


Given that `c = 1` and `c = 2` are predicates, and that • is a standard symbol,
we can transform the RHS of the rule into

    • ((c = 1 ∧ r1) ∨ (c = 2 ∧ r2))

Reasoning:

            (c=1 ∧ • r1) ∨ (c=2 ∧ • r2)
    equals  • (c=1 ∧ r1) ∨ • (c=2 ∧ r2)
    equals  • ((c=1 ∧ r1) ∧ (c=2 ∧ r2))

## Dealing with side conditions

If `l1 = tl1 ∧ pl1` and `l2 = tl2 ∧ pl2` then we can transform the lhs above
into `((c = 1 ∧ tl1) ∨ (c = 2 ∧ tl2)) ∧ ((c = 1 ∧ tp1) ∨ (c = 2 ∧ tp2))`

Then, using the distributivity of `∧` over `∨` we can factor out common 
predicates from the side condition.

Note: in the case we have the same predicate / term / variable / constant
in both rules, we can transform `(c = 1 ∧ t) ∨ (c = 2 ∧ t)` into
`t ∧ (c = 1 ∨ c = 2)`.

### Pushing choice predicates into terms


Let us generalize the property we stated above for `•` for any symbol in the
signature. We will prove that

    (c = 1 ∧ f(t11, .., t1n)) ∨ c = 2 ∧ f(t21, ..., t2n))

is equivalent to

    f((c = 1 ∧ t11) ∨ (c = 2 ∧ t21), ..., (c = 1 ∧ t1n) ∨ (c = 2 ∧ t2n))

Reasoning:

    f((c = 1 ∧ t11) ∨ (c = 2 ∧ t21), ..., (c = 1 ∧ t1n) ∨ (c = 2 ∧ t2n))
    equals   ∨     f(c = p(1) ∧ tp(1)1, ..., c = p(n) ∧ tp(n)n)
           p∈{1,2}ⁿ
    equals    ∨     (c = p(1) ∧ ... ∧ c = p(n) ∧ f(tp(1)1, ..., tp(n)n))
           p∈{1,2}ⁿ
    equals (c = 1 ∧ f(t11, ..., t1n)) ∨ (c = 2 ∧ f(t21, ..., t2n))

The last equality occurs because the cases where p is not constant 1 or 2 would
contain `c = 1 ∧ c = 2` as part of the disjunct, yielding `⊥`.

Note: When reaching a builtin construct we might choose not to push choices
further on.  If we do, then builtin unification would have to handle choices as
well.

### Indexed normal form

Applying the above we can compress two rules of the form

    axiom ∀ x1 . l1 ∧ p1 → • r1 ∧ p1'
    axiom ∀ x2 . l2 ∧ p2 → • r2 ∧ p2'

to something like:

    axiom ∀ x1 x2 c .
      G[(c = 1 ∧ t11) ∨ (c = 2 ∧ t21), ..., (c = 1 ∧ t1m) ∨ (c = 2 ∧ t2m)]
      ∧ ((c = 1 ∧ p1) ∨ (c = 2 ∧ p2))
      =>
      G'[(c = 1 ∧ t11') ∨ (c = 2 ∧ t21'), ..., (c = 1 ∧ t1n') ∨ (c = 2 ∧ t2n')]
      ∧ ((c = 1 ∧ p1') ∨ (c = 2 ∧ p2'))

Where `G` and `G'` are multi-hole contexts such that:

- `G[t11, ..., t1m] = l1` and `G[t21, ..., t2m] = l2`,
- `symbol(t1i) != symbol(t2i)` for each `1 <= i <= m`
- `G'[t11', ..., t1n'] = r1` and `G'[t21', ..., t2n'] = r2`,  
- `symbol(t1j') != symbol(t2j')` for each `1 <= j <= n`


Note 1: the restrictions on top symbols are optional; we might not want to
enforce maximal sharing.

Note 2: we can choose not to index the RHSs, in which case G' will be the empty
context

### Pushing choices to variable / constant level?

We could continue the pushing down process for the choice predicates even after
`symbol(t1i) != symbol(t2i)` for each `1 <= i <= m`, pushing the choices up to
the leafs.

Note, however, that this might not bring us additional benefits, because:

- having them at the junction point still propagates the choice predicate to
  the side condition for that branch
- all leafs would need to carry the choices to ensure not mixing up matches
- checking for conflicts between choices at end of unification is still needed


### Sharing variables?

Variables can be shared and there is no need to rename rules' variables;
indeed; the choice being exclusive, there is no danger of contagion between 
variables with the same name belogining to different rules, as the choice 
variable would make the whole substitution bottom if that happens.

On the other hand, care should be taken, as not renaming rules might allow
for the same identifier to be used with different sorts in the same combined
axiom, which might violate some existing assumptions.

### Example

When indexing the following two rules 

    rule <T> <k> (X:Id => V) ~> K:K </k>, <store> __(X ↦ V, Mem:Map) </store> </T>
    rule <T> <k> (X:Id := V => .K) ~> K:K </k>, <store> __(X ↦ (_ → V), Mem:Map) </store> </T>

The merged axiom might look of the form

    axiom
      <T>
        <k> _~>_(X:Id ∧ c = 1 ∨ X:Id := V ∧ c = 2, K:K ∧ (c = 1 ∨ c = 2))
        </k>
        <store>
            __(
                _↦_(
                    X ∧ (c = 1 ∨ c = 2),
                    (V ∧ c = 1) ∨ (Any ∧ c = 2)
                ),
                Mem:Map ∧ (c = 1 ∨ c = 2)
            )
        </store>
    => (c = 1 ∧ <T> <k> V ~> K </k> <store> __(X ↦ V, Mem) </store>)
       ∨
       (c = 2 ∧ <T> <k> .K ~> K </k> <store> __(X ↦ V, Mem) </store>)
        

Merging multiple rules
----------------------

When merging multiple rules, if not pushing choice predicates up to the
leaves, it makes sense to only insert them at the moment that a certain
rule diverges from all other rules. Rules sharing the same leaves will be
handled as described above.

### Example

Consider the following 4 rules:

    rule <k> (X:Exp / Y:Exp => X ~> []/ Y) ~> K:K </k>
      requires notBool(isKResult(X))

     rule <k> (X:Int / Y:Exp => Y ~> X:Int /[]) ~> K:K </k>
      requires notBool(isKResult(Y))
    
    rule <k> (X:Int / Y:Int => X /Int Y) ~> K:K </k>
      requires Y =/=Int 0
    
    rule <k> (X:Int / 0 => error("Division by 0!) ~> K:K) </k>

They could be merged into the following axiom:

    axiom
      <k>
        _~>_(
            _/_(
                (X:Exp ∧ c = 0)
                ∨
                inj{Int,Exp}(X:Int ∧ (c = 1 ∨ c = 2 ∨ c = 3))
            , (Y:Exp ∧ (c = 0 ∨ c = 1))
              ∨ inj{Int, Exp}(
                  (Y:Int ∧ c = 2)
                  ∨ (0 ∧ c = 3)
              )
            )

            ,
            K:K ∧ (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3)
        )
      </k>
      ∧
      ((c = 0 ∧ notBool(isKResult(X:Exp)))
       ∨
       (c = 1 ∧ notBool(isKResult(Y:Exp)))
       ∨
       (c = 2 ∧ Y:Int =/=Int 0)
       ∨
       c = 3
      )
    => (c = 0 ∧ <k> X:Exp ~> []/ Y:Exp ~> K </k>)
       ∨ (c = 1 ∧ <k> Y:Exp ~> X:Int /[] ~> K </k>)
       ∨ (c = 2 ∧ <k> X:Int /Int Y:Int ~> K </k>)
       ∨ (c = 3 ∧ <k> error("Division by 0") ~> K </k>)

On merging all-path / one-path claims
-------------------------------------

Since all-path claims are of the form `∀xᵢ.φᵢ → [w] ∃zᵢ.ψᵢ` where
`[w]` denotes the weak always finally operator, the reasoning above works,
yielding the following merged rule:


    axiom ∀ x1 x2 ... xn c .
      (c = 1 ∧ l1) ∨ ... (c = n ∧ ln) → [w] (c = 1 ∧ r1) ∨ ... (c = n ∧ rn)

We can then continue merging the lhs part as pointed above.

A similar argument applies for one-path claims.


All path reachability proofs
----------------------------
(See [All Path Reachability Proofs](2019-03-28-All-Path-Reachability-Proofs))

Assumption: in a goal to be proven, `∀x.φ → [w]∃z.ψ`, `φ` will be assumed to be
function-like.
This allows transforming any conjunction `φ ∧ γ` into the equivalent
`φ ∧ ⌈φ ∧ γ⌉`.



### Reinterpreting unification

The main idea is to transform `⌈φ ∧ γ⌉` through equivalences to a disjunction
of conjunctions of equalities between variables and terms representing a
substitution.  Using equivalences guarantees that a MGU is achieved.

In fact, the existing cases for unification stay the same; however, we now need
to take into account disjunctions and rule choice predicates.

For strongly deterministic definitions (using non-overlapping rules),
the unification itself will be deterministic, yielding substitutions
guarded by the choice predicate corresponding to the (only) rule unifying
with the current configuration.


### Reinterpreting the `derivePar` algorithm

Upone merging the one step axioms and the all path claims we interpret the
all-path algorithm as follows:

__Input__: goal `∀x.φ → [w]∃z.ψ`  and set of tuples `{ (xᵢ,φᵢ,zᵢ,ψᵢ) : 1 ≤ i ≤ n }`
representing either

+ a merged claim `∀x₁ x₂ ... xₙ c . l → [w] r`
+ a merged axiom `∀x₁ x₂ ... xₙ c . l → • ∃ z₁ ... zₙ . r`

where

+ `l ∧ (c = i)` is equal to φᵢ ∧ (c = i)` for `1 ≤ i ≤ n`,
   and `l ∧ (c = i)` is equal to `⊥` if `¬(i = 1) ∧ ... ∧ ¬(i = n)`
+ `r ∧ (c = i)` is equal to `ψᵢ ∧ (c = i)` for `1 ≤ i ≤ n`,
   and `r ∧ (c = i)` is equal to `⊥` if `¬(i = 1) ∧ ... ∧ ¬(i = n)`

__Output:__ `(Goal, goalᵣₑₘ)`

* Let `goalᵣₑₘ := ∀x.(φ ∧ ¬∃x₁ x₂ ... xₙ c .⌈φ ∧ l⌉) → [w]∃z.ψ`
* Let `Goal := ∀x z₁ z₂ ... zₙ.(∃x₁ x₂ ... xₙ c.r ∧ ⌈φ∧l⌉) → [w]∃z.ψ`


#### Argument for equivalence to the original algorithm

Say we want to prove `∀x.φ → [w]∃z.ψ`, and say we want to apply
circularities, i.e., the merged claim `∀x₁ x₂ ... xₙ c . l → [w] r`.


##### Unification predicate `⌈φ ∧ l⌉`

- `⌈φ ∧ l⌉` equals `⌈φ ∧ l⌉ ∧ ∃i.c=i`
- equals 
`∃i.⌈φ ∧ l⌉ ∧ c=i ∧ (i = 1 ∨ i = 2 ∨ ... ∨ i = n ∨ ¬(i = 1) ∧ ... ∧ ¬(i = n)`
- equals
`∃i.(⌈φ ∧ l⌉ ∧ c=i ∧ i = 1) ∨ (⌈φ ∧ l⌉ ∧ c=i ∧ i = 2) ∨ ... ∨ (⌈φ ∧ l⌉ ∧ c=i ∧ i = n) ∨ (⌈φ ∧ l⌉ ∧ c=i ∧ ¬(i = 1) ∧ ... ∧ ¬(i = n))`
- equals
`∃i.⌈φ ∧ l ∧ c=i ∧ i = 1⌉ ∨ ⌈φ ∧ l ∧ c=i ∧ i = 2⌉ ∨ ... ∨ ⌈φ ∧ l ∧ c=i ∧ i = n⌉ ∨ ⌈φ ∧ l ∧ c=i ∧ ¬(i = 1) ∧ ... ∧ ¬(i = n)⌉`
- equals
`∃i.⌈φ ∧ l ∧ c=i ∧ i = 1⌉ ∨ ⌈φ ∧ l ∧ c=i ∧ i = 2⌉ ∨ ... ∨ ⌈φ ∧ l ∧ c=i ∧ i = n⌉ ∨ ⌈φ ∧ l ∧ c=i ∧ ¬(i = 1) ∧ ... ∧ ¬(i = n)⌉`
- equals
`∃i.⌈φ ∧ φ₁ ∧ c = i ∧ i = 1⌉ ∨ ⌈φ ∧ φ₂ ∧ c = i ∧i = 2⌉ ∨ ... ∨ ⌈φ ∧ φₙ ∧ c = i ∧ i = n⌉ ∨ ⌈φ ∧ ⊥ ∧ ¬(i = 1) ∧ ... ∧ ¬(i = n)⌉`
- equals
`∃i.(⌈φ ∧ φ₁⌉ ∧ c = i ∧ i = 1) ∨ ∃i.(⌈φ ∧ φ₂⌉ ∧ c = i ∧ i = 2) ∨ ... ∨ ∃i.(⌈φ ∧ φₙ⌉ ∧ c = i ∧ i = n)`
- equals
`(⌈φ ∧ φ₁⌉ ∧ c = 1) ∨ (⌈φ ∧ φ₂⌉ ∧ c = 2) ∨ ... ∨ (⌈φ ∧ φₙ⌉ ∧ c = n)`

#### `goalᵣₑₘ`

`goalᵣₑₘ` equals `∀x.(φ ∧ ¬∃x₁ x₂ ... xₙ c .⌈φ ∧ l⌉) → [w]∃z.ψ`
- equals (from the above)
`forall x. (φ ∧ ¬∃x₁ ... xₙ c . ((⌈φ ∧ φ₁⌉ ∧ c = 1) ∨ (⌈φ ∧ φ₂⌉ ∧ c = 2) ∨ ... ∨ (⌈φ ∧ φₙ⌉ ∧ c = n))) → [w]∃z.ψ`
- equals (FOL manipulation)
`forall x. (φ ∧ ¬(∃x₁ ... xₙ . ⌈φ ∧ φ₁⌉ ∨  ... ∨  ∃x₁ ... xₙ .⌈φ ∧ φₙ⌉)) → [w]∃z.ψ`
- equals (xᵢ distinct, φᵢ contains only xᵢ, φ does not contain any of the xᵢs)
`forall x. (φ ∧ ¬(∃x₁. ⌈φ ∧ φ₁⌉ ∨  ... ∨  ∃xₙ .⌈φ ∧ φₙ⌉)) → [w]∃z.ψ`
- equals (¬ distribution)
`forall x. (φ ∧ ¬∃x₁. ⌈φ ∧ φ₁⌉ ∧  ... ∧ ¬∃xₙ .⌈φ ∧ φₙ⌉) → [w]∃z.ψ`
which is precisely the remainder from the original `derivePar` algorithm

##### Goal

`Goal` equals `∀x z₁ z₂ ... zₙ.(∃x₁ x₂ ... xₙ c.r ∧ ⌈φ∧l⌉) → [w]∃z.ψ`
- equals
`∀x z₁ z₂ ... zₙ.(∃x₁ x₂ ... xₙ c.r ∧ ((⌈φ ∧ φ₁⌉ ∧ c = 1) ∨ (⌈φ ∧ φ₂⌉ ∧ c = 2) ∨ ... ∨ (⌈φ ∧ φₙ⌉ ∧ c = n))) → [w]∃z.ψ`
- equals (distributivity)
`∀x z₁ z₂ ... zₙ.(∃x₁ x₂ ... xₙ c.(r ∧ ⌈φ ∧ φ₁⌉ ∧ c = 1) ∨ (r ∧ ⌈φ ∧ φ₂⌉ ∧ c = 2) ∨ ... ∨ (r ∧ ⌈φ ∧ φₙ⌉ ∧ c = n)) → [w]∃z.ψ`
- equals (rules for `r`)
`∀x z₁ z₂ ... zₙ.(∃x₁ x₂ ... xₙ c.(ψ₁ ∧ ⌈φ ∧ φ₁⌉ ∧ c = 1) ∨ ... ∨ (ψₙ ∧ ⌈φ ∧ φₙ⌉ ∧ c = n)) → [w]∃z.ψ`
- equals (FOL manipulation)
`∀x z₁ z₂ ... zₙ.(∃x₁ x₂ ... xₙ .(ψ₁ ∧ ⌈φ ∧ φ₁⌉) ∨ ... ∨ ∃x₁ x₂ ... xₙ .(ψₙ ∧ ⌈φ ∧ φₙ⌉)) → [w]∃z.ψ`
- equals (xᵢ distinct, φᵢ and ψᵢ contain only xᵢ, φ does not contain any of the xᵢs)
`∀x z₁ z₂ ... zₙ.(∃x₁.(ψ₁ ∧ ⌈φ ∧ φ₁⌉) ∨ ... ∨ ∃xₙ.(ψₙ ∧ ⌈φ ∧ φₙ⌉)) → [w]∃z.ψ`
- equals (FOL manipulation
`(∀x z₁ z₂ ... zₙ.∃x₁.(ψ₁ ∧ ⌈φ ∧ φ₁⌉) → [w]∃z.ψ) ∧ ... ∧  (∀x z₁ z₂ ... zₙ.∃xₙ.(ψₙ ∧ ⌈φ ∧ φₙ⌉)) → [w]∃z.ψ`
- equals (zᵢ distinct, ψᵢ contains only zᵢ, φ, φᵢ does not contain any of the xᵢs, and all types are inhabited)
`(∀x z₁.∃x₁.(ψ₁ ∧ ⌈φ ∧ φ₁⌉) → [w]∃z.ψ) ∧ ... ∧  (∀x zₙ.∃xₙ.(ψₙ ∧ ⌈φ ∧ φₙ⌉)) → [w]∃z.ψ`

Which is precisely the conjunction of `Goals` from the original `derivePar` algorithm. 

