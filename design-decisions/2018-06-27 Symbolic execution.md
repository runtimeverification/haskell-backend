Symbolic Execution in K
=======================

Problem Setup
-------------

Given a theory T as a Kore definition and a symbolic pattern phi representing the current term of execution, the one-step symbolic execution engine should produce a pattern psi such that:

1. T |- phi => psi
1. For any psi’ such that T |- phi => psi’, we have T |- psi -> psi’.
1. A proof object that witnesses (1).

A more detailed specification of the one-step symbolic execution engine is given in [Section 2](#One-Step-Symbolic Execution API).

In general, the Kore definitions consist of the following parts:

- Definitions of all language constructs and related axioms (the concrete syntax of the programming language);
- Definitions of domain theories (e.g. Int, String, Map, etc. Domain theories are often hooked to external libraries, and thus may introduce gaps in proof objects.)
- Definitions of cells and configuration. From a theoretical point of view, cells are also defined as matching logic symbols as language constructs, but backends may implement cells differently in order to support efficient matching modulo axioms.
- Definitions of rewrite contexts and rewrite rules.

### How to encode K rules as Kore axioms?

Ideally, the encoding should require no intelligence at all. In the following, we consider various common forms of K rules, and give their corresponding axioms in Kore.

```
rule lhs => rhs
-------------------------
axiom C[lhs => rhs]
```

```
rule lhs => rhs requires cond
------------------------------------
axiom (cond = true) -> C[lhs => rhs]
```

Sometimes, the rewrite may appear in some context (e.g. in a specific cell or in a specific language construct).

```
rule Context[lhs => rhs]
-----------------------------------
axiom C[Context[lhs => rhs]]
```

As an example, consider the lookup rule
```
rule <T>
       <k> (X => I) ~> REST </k>
       <state> M1 (X |-> I) M2 </state>
     </T>
----------------------------------------
axiom C[Tcell(kcell(arrow((X => I), REST)),
              statecell(merge(merge(M1, bind(X, I)), M2)))]
```

Sometimes, multiple rewrites may happen in a rule.

```
rule Context[lhs1 => rhs1, …, lhsn => rhsn]
-----------------------------------------------
axiom C[Context[lhs1 => rhs1, …, lhsn => rhsn]]
```

As an example, consider the assignment rule
```
rule <T>
       <k> (X := I; => .) ~> REST </k>
       <state> M1 (X |-> (J => I)) M2 </state>
     </T>
-----------------------------------------------------------------
axiom C[Tcell(kcell(arrow((X := I => nothing), REST)),
              statecell(merge(merge(M1, bind(X, (J => I))), M2)))]
```

Frontend syntax may be different. For example, the same assignment rule may be preferably written as:
```
rule  <k> (X := I; => .) ~> REST </k>
      <state> M1 (X |-> (J => I)) M2 </state>
```
or simpler:
```
rule  <k> (X := I; => .) ... </k>
      <state> ... (X |-> (J => I)) ... </state>
```
or simpler:
```
rule ... (X := I; => .) ... (X |-> (J => I)) ...
```

Rules may be encoded differently, too. For example, the last rule above may also be encoded as axiom using multihole context:
```
axiom C[(X := I; => .), (X |-> (J => I)]
```

### The need for Kore-to-Kore translation.

As we have seen, frontend syntax is different. And frontend may encode rules differently. Some encodings might be straightforward for frontends but would require backends to do more intelligent tasks (such as figuring out multihole contexts, matching modulo axioms, etc.). Some encodings might be easy for backends to execute programs, but would require more intelligent tasks from frontend (such as completing configuration and cells).

Our proposal is the follows. We let frontends generate Kore definition, denoted as Kore0. Then, we translate (compile) this Kore definition to another Kore definition, denoted as Kore1, which is “easier for backends”. This process may keep going for a while, and we will have a chain of Kore definitions:

`Kore0 ---> Kore1 ---> Kore2 ---> … ---> Kore_n`

Ideally, the final Kore definition Kore_n will be easy enough for backend to execute programs.

Here, we are interested in symbolic execution (backends), so we will assume that we have the final Kore definition Kore_n in hand.

### Assumptions about the final Kore definition Kore_n

- It uses no contexts;
- It uses no matching modulo axioms;
- Please add.

One-Step Symbolic Execution API
-------------------------------

### General Results.

### One-Step One-Rule Global Unconditional Functional Pattern Symbolic Execution

“Global” means the rewrite rule has the form `lhs => rhs`, with the rewrite happens in the top.
“Unconditional” means the rewrite rule has no condition.
“Functional” means that lhs, rhs and the symbolic term phi are all functional patterns. This simplifies the Unification procedure.

The major API is a step function that takes a Kore definition, a symbolic pattern representing the current term, and a rewrite rule (as an axiom in Kore), and generates a pattern psi representing the result of applying the rewrite rule on the current term. The function should also generate a proof object as a certification. We will discuss what the proof is for and how to generate it later.

```
step :: Definition {- T -}
     -> Pattern    {- phi /\ C -}         // a functional pattern
                                          // with a predicate C
     -> Rule       {- r -}           // an unconditional global rule
     -> (Pattern   {- psi -}, Proof)
```

Notice that the rule `r` is just a pattern (which is an axiom in T).

#### Assumptions

Here are our assumptions.

1. phi is a functional pattern consisting of only constructors and variables (no logic connectives is allowed); Notice that by definition constructors are neither assoc or comm (otherwise they are not injective);
1. C is a predicate pattern; all free variables in C appear in phi;
1. r has the form `lhs => rhs`, where lhs and rhs are functional patterns;
1. lhs and rhs are configuration completed;
1. lhs consists of only constructors and variables;
1. rhs consists of only symbols (both constructors and defined functions) and variables (no logic connectives is allowed);
1. all variables in rhs appear in lhs;
1. there is at most a functional pattern t and a predicate pattern s (expressing a substitution) s.t. `t /\ s = (phi /\ lhs)`.
1. Variables in lhs and rhs are fresh, i.e., they do not appear in the definition T, the current pattern phi, the predicate C, and any pattern in any proof objects where lhs and rhs appear.

We will need quite a few simplification procedures for different scenarios. The following simplification procedure is the one that is needed for Basic Symbolic Execution. It does existential quantification elimination by applying a substitution on a pattern. For example, it simplifies `\exists y . (y = t) /\ rhs` to `rhs[t/y]` if y doesn’t occur in t.

#### Basic Simplification (Existential Quantification Elimination)

**Input:** a pattern rhs, a predicate pattern subst (of the following form), and a variable yi:

- subst has the form `y1 = t1 /\ … /\ yk = tk`, where `y1 … yk` are distinct variables and `t1 … tk` are patterns which do not contain `y1 … yk`;

**Output:** a pattern psi and a predicate pattern D such that

- `|- (\exists yi. rhs /\ subst) = psi /\ D`

**Algorithm:**

1. If yi is not in y1 … yk, do nothing (stop unsuccessfully);
1. If yi appears in ti, do nothing (stop unsuccessfully);
1. Return (rhs /\ y1 = t1 /\ … y_{i-1}= t_{i-1} /\ y_{i+1} = t_{i+1} /\ … /\ yk = tk) [ ti / yi ]

**Proof Object Generation:** TBA

#### Basic Unification

**Input:** `phi /\ lhs`

**Output:** a functional pattern t, a predicate subst representing the substitution, such that

1. `T |- phi /\ lhs = t /\ subst`;
1. All free variables in t and subst must have free occurrence in phi or lhs;
1. subst is either bottom, indicating that the unification fails, or has the form `y1 = t1 /\ … /\ yk = tk`, where `y1 … yk` are distinct variables appearing in phi or lhs and `t1 … tk` are functional patterns consisting of only constructors and variables other than `y1 … yk`; All variables in lhs should appear in `y1 … yk`.

**Algorithm:** TBA.

**Proof Object Generation:** TBA

#### Basic Symbolic Execution

**Input:** `phi /\ C`, `lhs => rhs`

**Output:** a functional pattern psi and a predicate pattern D satisfying the same assumptions we put on phi and C such that

- `|- (phi /\ C) -> ((\exists v . lhs) => psi /\ C /\ D))`

**Algorithm:**

1. Call *Basic Unification* on phi /\ llhs and obtain t and subst.
1. Let v be all free variables in lhs. Call *Simplification Procedure* on \exists v . (subst /\ rhs) and obtain a pattern psi /\ D, where psi is a functional pattern and D is a predicate pattern;
1. Return psi and D.

**Proof Object Generation.**

1. `lhs => rhs`  // by axiom
1. `lhs -> X rhs` // by (1) and definition of `_=>_`. Here X means the strong-next.
1. `lhs /\ \ceil(lhs /\ phi) -> (X rhs) /\ \ceil(lhs /\ phi)` // by (2) and propositional reasoning
1. `lhs /\ \ceil(lhs /\ phi) = lhs /\ phi` // by ML paper Prop. 5.24
1. `lhs /\ phi -> (X rhs) /\ \ceil(lhs /\ phi)` // by (3) and (4)
1. `lhs /\ phi = t /\ subst` // by Unification Procedure
1. `lhs /\ phi -> subst /\ X rhs` // by (5) (6) Prop 5.12 and \ceil(t) = \top
1. `lhs /\ phi /\ C -> subst /\ C /\ X rhs` // by (7) and prop reasoning
1. `lhs /\ phi /\ C -> \exists v . (subst /\ C /\ X rhs)` // by (8) FOL reasoning
1. `lhs /\ phi /\ C -> X (C /\ \exists v . (rhs /\ subst))` // by (9) Propagation and v not free in C
1. `\exists v . (rhs /\ subst) = psi /\ D` // by (recursively calling) *Basic Simplification*
1. `lhs /\ phi /\ C -> X (C /\ psi /\ D)` // by (10) and (11)
1. `\forall v . (lhs /\ phi /\ C -> X (C /\ psi /\ D))` // by (12)
1. `(\exists v . lhs) /\ phi /\ C -> X (psi /\ C /\ D)` // by (13), FOL reasoning, and Prop 5.12
1. `phi /\ C -> ((\exists v . lhs) -> X (psi /\ C /\ D))` // by (14) and prop reasoning
1. `phi /\ C -> ((\exists v . lhs) => (psi /\ C /\ D))` // by (15), definition of => and psi

**Remarks.**

- Notice that psi is the result of applying subst on rhs (See proof step 11). If there are defined symbols (aka non-constructor symbols such as +Int) in rhs, they will also appear in subst. We could then “evaluate” those defined symbols by rewriting psi using the oriented equations that define those symbols. This procedure should be another simplification procedure.

- Notice that in Step (11), we can call Basic Simplification to remove all existential quantification \exists v, because Basic Unification guarantees that subst must have the form `y1 = t1 /\ … /\ yk = tk` and all variables in lhs (i.e. v) appear in the list.


Stop reading here. The following will be moved to the above.
------------------------------------------------------------



```
Xiaohong: I guess the Proof here is just a proof of (1)? I don’t think we could ever generate a proof for (2) (not even with the meta-level and the meta-theory), because it looks like a high-order property.
Now, to determine such a psi, we need to:
Identify all rules having the same sort as psi
This might require some sort parameters instantiation
[Xiaohong] This might require some reasoning with injective functions (from subsorts to their super sorts)
Build a disjunction D over of all rules of same sort as psi
Need fresh instances of the rules
Constructors for Conjunction and Disjunction over a list?
I am not sure we want to jump into (2) and consider disjunction of all rules right now. How about we just consider one rule as a starting point?
Conjunct phi with  D and simplify

Distribute conjunction over D
For each disjunction
Push conjuncts down
If not unifiable, discard disjunct
Push substitution up
Solve unification subproblems
Push implication up
Apply substitution
The resulting pattern now should look something like:
(phi -> \next psi_1) \/ (phi -> \next psi_2) \/ … \/ (phi -> \next psi_n)
Factor phi out to phi -> \next psi_1 \/ \next psi_2 \/ … \/ \next psi_n and choose phi’ to be \next psi_1 \/ \next psi_2 \/ … \/ \next psi_n

Xiaohong’s draft:

I tried to work out some maths and concrete examples, just for me to understand the thing better. Hope it may also help to clarify things.

Notations: X phi means \next (phi). lhs => rhs means \rewrites(lhs, rhs), which is just lhs -> X rhs.   phi -> phi’ means implication.

Question 1: If phi /\ (lhs => rhs)  <->   ((phi /\ lhs) => rhs)?
The implication from left to right is true. To see it:
phi /\ (lhs -> X rhs) -> (phi /\ lhs) -> X rhs   // by definition of P => Q === P -> X Q
which is a propositional tautology.
The other implication is not always true (in fact mostly it’s untrue).

Question 2: If (phi /\ subst -> X rhs) <-> ((phi -> X rhs) /\ subst) ?
We do a semantic proof. Since subst is a conjunction of equalities, we do a case analysis on whether subst is /top or /bottom. If it is /top, then clearly the double implication holds because both sides are phi -> X rhs. If it is /bottom, then the left hand side of the implication becomes /top while the right hand side becomes /bottom.
Therefore, the implication from right to left always holds. The implication from left to right holds if and only if subst is \top. In particular, |- left -> right iff |- subst. Notice that it is very unlikely that we can prove |- subst (see the concrete example in the following). Therefore, it is very unlikely that we can prove |- left -> right.

A walk-through of (3):
Suppose the rule is inj(I1) + inj(I2) => inj(I1 +Int I2), and the current term phi is inj(3) + inj(4).
Here the syntax is AExp ::= inj(Int) | AExp “+” AExp. Think of inj as the injective function from Int to AExp.
We expect that one-step symbolic execution gives us inj(3 +Int 4), together with a proof of
|- inj(3) + inj(4) => inj(3 +Int 4).

Here’s is a walk-through of (3):

(3) Conjunct phi with D and simplify
Here D is just a single rule. So the conjunction is just
inj(3) + inj(4)   /\    inj(I1) + inj(I2) => inj(I1 +Int I2)       // pattern (P1)

(a) Distribute conjunction over D
There is just one rule in D so no action needed here.

(b) For each disjunction

(i) Push conjuncts down. Use the result in Question 1, we can conjunct with the l.h.s. of the rule only and obtain the following pattern (P2), for which we can prove |- P1 -> P2:
(inj(3) + inj(4) /\ inj(I1) + inj(I2)) => inj(I1 +Int I2)       // pattern (P2)

(i1) Solve the conjunction and obtain a mgu and a substitution (this only works for functional patterns (see Proposition 5.24 (3) of the Matching Logic paper), so we need two additional proofs that inj(3) + inj(4) and inj(I1) + inj(I2) are both functional patterns.)
(inj(I1) + inj(I2)) /\ (I1 = 3) /\ (I2 = 4) => inj(I1 +Int I2)   // pattern (P3) which is equivalent to (P2)

(ii) Push substitution up, and we get
((inj(I1) + inj(I2)) => inj(I1 +Int I2))  /\ (I1 = 3) /\ (I2 = 4) // pattern (P4)
From Question 2, we know that |- (P4) -> (P3). However, |- (P3) -> (P4) iff |- subst, and in our case, it is |- I1 = 3 /\ I2 = 4, which, unfortunately, is wrong. We cannot prove |- I1 = 3 /\ I2 = 4, and thus we cannot prove |- (P3) -> (P4). Notice that now we lose the connection between (P1) and (P4): We only know (P1) -> (P2), (P2) <-> (P3), and (P4) -> (P3).

(iii) Solve subunificiation problems.
There’s no more unification problems. No action needed.

(iv) Push implication up
(I guess) The implication is already at the top. No action needed.

(v) Apply substitution and we get
((inj(3) + inj(4)) => inj(3 +Int 4))  /\ (I1 = 3) /\ (I2 = 4) // pattern (P5) which is equivalent to (P4)

As we have seen, we lose connection between (P5) and the original (P1). Also, I think we shouldn’t introduce new variables (from the rules) as we do one-step symbolic execution (unless the rules explicitly want that. Normally a rule should not use variables in its rhs that don’t appear in its lhs). Therefore, after (v), we should apply an additional step:
(vi) Existentially quantify all the free variables in rules:
exists I1 I2 . ((inj(3) + inj(4)) => inj(3 +Int 4))  /\ (I1 = 3) /\ (I2 = 4) // pattern (P6)

And simply it by quantification elimination:
((inj(3) + inj(4)) => inj(3 +Int 4))  // pattern (P7)


A revision of the algorithm

My observation is that in step (i), we anyway need to “conjunct the current term with the lhs of the rule”. Therefore, it makes sense to have a function get-lhs, which takes a rule R and returns its lhs. And thus it makes sense to have a similar function get-rhs that returns its rhs. Once we have these two functions, let us denote lhs = get-lhs(R) and rhs = get-rhs(R).
Define phi’ as follows:
phi’ = exists v . \ceil(lhs /\ phi) /\ rhs    // v is all free variables in lhs
Notice phi’ doesn’t contain any free occurrence of v.

Then there are two separate tasks. One is to simply phi’, and the other is to generate a proof of |- phi => phi’. Let’s first see how to simply phi’.

Task 1: Simplify phi’.
Call Unification Procedure on lhs /\ phi, the unification procedure should return a substitution (denoted as subst), and a proof |- lhs /\ subst = phi /\ subst (maybe?)
Use subst to eliminate the existential quantification on top of phi’ and obtain a simplified phi’’, together with a proof |- phi’ = phi’’. (We need to figure out the details here).

Task 2: Prove |- phi => phi’
Basically we need to prove |- phi -> X ( exists v . \ceil(lhs /\ phi) /\ rhs )
Notice that by semantic axioms, we can prove |- lhs -> X rhs, and thus:
|- (\ceil(lhs /\ phi) /\ lhs) -> \ceil(lhs /\ phi) /\ X rhs   // by semantics and propositional reasoning
|- (\ceil(lhs /\ phi) /\ lhs) -> X (\ceil(lhs /\ phi) /\ rhs)  // by Proposition 5.12 in the ML paper
|- (lhs /\ phi) -> X (\ceil(lhs /\ phi) /\ rhs) // by Propositiona 5.24 (lhs /\ phi) = (\ceil(lhs /\ phi) /\ lhs)
|- (lhs /\ phi) -> exists v .  X (\ceil(lhs /\ phi) /\ rhs) // by FOL reasoning (YES! We used exists)
|- (lhs /\ phi) -> X exists v . (\ceil(lhs /\ phi) /\ rhs)  // by Propagation-Exists
|- forall v . ((lhs /\ phi) -> X phi’)  // by (Universal Generalization)
|- (exists v . lhs) /\ phi -> X phi’   // by FOL reasoning, and v doesn’t occur free in phi and phi’
|- (exists v . lhs) /\ phi => phi’   // by definition of _=>_

Notice that this is exactly what we want. It says that the part of phi that can be matched by the left hand side of rules, i.e., (exists v . lhs) /\ phi, can rewrite to phi’ in one-step. This captures exactly the semantics of \next, which is strong next (not weak next).

In other words, the one-step symbolic execution can tell us two things.
when (or which part of) a term phi can be executed by the semantics, and how. The answer is that (exists v . lhs) /\ phi can be executed to phi’ in one-step.
When (or which part of) a term phi is terminating / blocking. The answer is simply (not exists v . lhs) /\ phi.

I think the above discussion can be easily extended to multiple rules, either process them one by one and then merge the result, or simply merge them into one rule.

Still, there’s the question of how to compute the l.h.s. and r.h.s. of a rule R. When R is the so-called global rewrite rule that has the form lhs => rhs, it’s easy. However in K, many rules are local rewrite rules (for example the lookup rule and the assignment rule). My guess is that for local rewrite rule R, simply define get-lhs(R) = R [ lhs1 / lhs1 => rhs1] … [lhsk / lhsk => rhsk] and similarly for get-rhs.

--------------------------------
[Traian] Ok, I think I got it wrong the first time, but let me try one more time, maybe it becomes clearer:
First, note that I was wrong in saying that phi needs to be conjoined with the conjunction of rules, because all rules hold, and we want to see what comes out of phi and the rules.

Anyway, let’s forget about it for now, and see what comes out of phi and a rule.

Phi /\ (lhs -> X rhs) <-> phi /\ (not lhs \/ X rhs) <-> (by boolean reasoning) phi /\ (not lhs \/ (lhs /\ X rhs)) <-> (distributivity) (phi /\ not lhs) \/ (phi /\ lhs /\ X rhs)

So I think this gets me to your points (1) and (2) above, so we are in agreement so far.

However, I would like to avoid pushing rewrites to the top.
Now, let F be a functional constructor symbol.  We have that:
F(phi) /\ F(lhs -> X rhs) -> F(phi /\ (lhs -> rhs)) <->... (by the argument above) …<->
F((phi /\ not lhs) \/ (phi /\ lhs /\ X rhs)) <->(by propagation of \/)
F(phi /\ not lhs) \/ F(phi /\ lhs /\ X rhs) <-> (by Prop 5.24 (lhs /\ phi) = (\ceil(lhs /\ phi) /\ lhs)))
F(phi /\ not lhs) \/ F(phi /\ \ceil(lhs /\ phi) /\ X rhs) <-> (by constraint propagation)
F(phi /\ not lhs) \/ (F(phi /\ X rhs) /\ \ceil(lhs /\ phi))

And here, I am again stuck.  Any suggestions?
```
