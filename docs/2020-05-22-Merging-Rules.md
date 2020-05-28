# Rationale

Rule application can benefit from indexing of rules and using efficient
data-structures to decide faster which rule can be applied on a given
configuration.

This document attempts to justify this approach from a provability point of
view, to ensure that the indexing algorithms are provably sound.

# Background

K rules, are of the form

    rule l => r requires c

where, in general, l is a constructor-based term
(modulo axioms: may contain Ac constructors, overloadable constructors)

When translated into matching logic, they are of the form

    axiom l ∧ c → EX r

Where EX is the next operator, meaning that there is a possible transition
from l (satisfying c) to r.

# Approach

We will only discuss here combining two rules, but it should be clear
that this easily extends to any finite number of rules.

## FOL interlude

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

## Back to ML

Given two rules

    axiom ∀ x1 . l1 → EX r1
    axiom ∀ x2 . l2 → EX r2

From the theorem above, we can combine the two axiom into an equivalent one:

    axiom ∀ c x1 x2 .
        (c = 1 ∧ l1) ∨ (c = 2 ∧ l2) →
        (c = 1 ∧ EX r1) ∨ (c = 2 ∧ EX r2)


Given that `c = 1` and `c = 2` are predicates, and that EX is a standard symbol,
we can transform the RHS of the rule into

    EX ((c = 1 ∧ r1) ∨ (c = 2 ∧ r2))

Reasoning:

            (c=1 ∧ EX r1) ∨ (c=2 ∧ EX r2)
    equals  EX (c=1 ∧ r1) ∨ EX (c=2 ∧ r2)
    equals  EX ((c=1 ∧ r1) ∧ (c=2 ∧ r2))

## Side conditions

If `l1 = tl1 ∧ pl1` and `l2 = tl2 ∧ pl2` then we can transform the lhs above
into `((c = 1 ∧ tl1) ∨ (c = 2 ∧ tl2)) ∧ ((c = 1 ∧ tp1) ∨ (c = 2 ∧ tp2))`

Then, using the distributivity of `∧` over `∨` we can factor out common 
predicates from the side condition.

Note: in the case we have the same predicate / term / variable / constant
in both rules, we can transform `(c = 1 ∧ t) ∨ (c = 2 ∧ t)` into
`t ∧ (c = 1 ∨ c = 2)`.

## Pushing choice predicates into terms


Let us generalize the property we stated above for `EX` for any symbol in the
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

    axiom ∀ x1 . l1 ∧ p1 → EX r1 ∧ p1'
    axiom ∀ x2 . l2 ∧ p2 → EX r2 ∧ p2'

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

## Pushing choices to variable / constant level?

We could continue the pushing down process for the choice predicates even after
`symbol(t1i) != symbol(t2i)` for each `1 <= i <= m`, pushing the choices up to
the leafs.

Note, however, that this might not bring us additional benefits, because:

- having them at the junction point still propagates the choice predicate to
  the side condition for that branch
- all leafs would need to carry the choices to ensure not mixing up matches
- checking for conflicts between choices at end of unification is still needed


## Sharing variables?

Variables can be shared and there is no need to rename rules' variables;
indeed; the choice being exclusive, there is no danger of contagion between 
variables with the same name belogining to different rules, as the choice 
variable would make the whole substitution bottom if that happens.

On the other hand, care should be taken, as not renaming rules might allow
for the same identifier to be used with different sorts in the same combined
axiom, which might violate some existing assumptions.

#### Example

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
        

### Multiple rules

When merging multiple rules, if not pushing choice predicates up to the
leaves, it makes sense to only insert them at the moment that a certain
rule diverges from all other rules. Rules sharing the same leaves will be
handled as described above.

#### Example

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
