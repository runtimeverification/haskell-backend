Reachability symbols
====================

Below is a list of LTL/CTL/Reachability Logic symbols and their translation to mML.

For further reference, consult the LICS ML paper and the corresponding technical report.

### One-path next `•`
---------------------

One path next is a reserved symbol in any mML signature used for representing 𝕂 definitions,
used to express possibility of transition and thus to encode 𝕂 transition rules.

for example, a 𝕂 rule
```
rule a => b
```
is represented in mML as 
```
axiom a → •b
```

Semantically, `•b` comprises the set of all elements which can transition to `b` in one step.

Hence, `a → •b` is read as `a` __can__ transition to `b` in one step.

(Strong) Eventually (LTL) `◇` or `<>` or Exists Finally (CTL∗) `EF`
-------------------------------------------------------------------

`◇ φ` says that there exists a finite path leading to `φ`.

`φ → ◇ ψ` says that any state satisfying `φ` can transition in a finite number of steps to 
a state satisfying `ψ`.

In mML `◇` is defined as a smallest fixpoint (guaranteeing finite paths) by the alias formula
```
◇ φ := μX.φ ∨ •X
```

(Weak) Eventually (One-path reachability) `◇w` or `wEF`
-------------------------------------------------------

`◇w φ` says that there exists an infinite path or a finite path leading to `φ`

`φ → ◇w ψ` says that any state satisfying `φ` can either transition indefinitely,
or transition in a finite number of steps to a state satisfying `ψ`.

In mML `◇w ` is defined as a greatest fixpoint by the alias formula
```
◇w  φ := νX.φ ∨ •X
```


All-path next `○`
-----------------

All-path next is the dual of one-path next.  It is defined as an alias formula by:
```
○ φ := ¬•¬φ
```

Semantically, `○ A` comprises those elements which, if they can transition,
then they __must__ transition to `A`.

Hence, `φ → ○ ψ` is read as "all possible continuations of `φ` in one step must satisfy `ψ`".

Note that the above holds even if `φ` is "stuck", i.e., cannot transition anymore.
Therefore, an useful formula, stating that `φ` __must__ transition to `ψ` in one step
(hence, it is aditionally not stuck) is:
```
φ → ○ ψ ∧ •⊤
```

(Strong) Always (LTL) `□` or `[]` or Always Globally (CTL∗) `AG`
----------------------------------------------------------------

`□ φ` says that `φ` always holds (on all paths, at all times).

In mML `□` is defined as a greatest fixpoint by the alias formula
```
□ φ := νX.φ ∧ ○ X
```

(Weak) Always Finally (All-Path reachability) `[w]` or `wAF`
------------------------------------------------------------

`wAF φ` says that paths either contain a state in which `φ` holds, or they are
infinite.

Hence `φ → wAF ψ` states that for any state satisfying `φ`, there are no
finite paths on which `ψ` does not eventually hold.

In mML `wAF` is defined as a greatest fixpoint by the alias formula
```
wAF  φ := νX.φ ∨ (•T ∧ ○ X)
```

Well foundness (termination) `WF`
---------------------------------

`WF` expresses that there are no infinite paths.

Hence `φ → WF` says that there are no infinite paths starting from `φ`.

`WF` is defined in mML by the least fixpoint alias
```
WF := μX.○ X
```
