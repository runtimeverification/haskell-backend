Unification (new)
=================

This document attempts to describe the proposed new unification algorithm.  This is divided into two sections: the algorithm itself, and an appendix how to unify various types of terms. 

The algorithm is fairly straightforward: we construct a priority queue of pairs of terms representing subterms to be unified. The queue is initialized with the two top-level terms. We then repeatedly pop pairs of terms from the priority queue and process them. Each pair can result in one of five actions:

1. *Discharge* the pair if unification of these two terms succeeds unconditionally.
2. *Fail* the entire unification procedure if these two terms do not unify.
3. *Bind* a variable to a term.
4. *Decompose* the terms into one or more new pairs, adding them to the priority queue.
5. *Add a constraint* in the event that unification can only be solved partially.
6. *Add an AC equation* in the event that AC unification is required.

Obviously because of *bind* and *constraint* operations, we must maintain a map binding variable names to terms, a set of variable names contained in the mgu, and a list of constraints. When adding constraints, we always substitute the current mgu into the resulting term, simplify, and evaluate any equations before proceeding.

After the priority queue is empty, we still need to solve the AC subproblems. This process is described in the Map section below. It will generate a disjunction of substitutions. We then cross product the disjunctions from the Map and Set subproblems, and conjunct it with the mgu. This becomes the final set of unifiers.

If we did not fail anywhere, unification succeeds.  We then return the set of unifiers.

One detail not yet discussed concerns the ordering of pairs within the priority queue. Essentially, there are only three levels of operations: deterministic operations, operations requiring recursive unification, and nondeterminstic operations. These proceed in order with deterministic operations happening first and nondeterministic operations happening last.

The only cases involving recursive unification are `#if #then #else #fi` and the case unifying term equality with `false`. The only nondeterministic cases involve maps and sets. All other cases are deterministic.

Below is the appendix dealing with how to process each type of pattern.

Aliases
-------

If either pattern is an alias, expand that alias and decompose with the expanded terms.

Top and Bottom
--------------

If either term is \bottom, fail.
Otherwise, if either term is \top, discharge.

Constants
---------

If both terms are \dv, and are equal, discharge.
If they are unequal, fail.

Variables
---------

If both terms are the same variable A, discharge.
If both terms are variables A and B, and both are free, bind A to B and add A to the mgu.
If one is free (A) and the other is bound (B), bind A to B and add A to the mgu.
If both are bound, decompose with their bindings.

If one term is a variable A and the other is a function-like pattern p, if A is free, bind A to p and add A to the mgu.
Otherwise (A is bound), if it is bound to a free variable B, bind B to p.
Otherwise (B is bound to a pattern), decompose with the pattern and B's binding.

Constructors
------------

If the first term is injective and the second is the same symbol, decompose with each pair of children of each pattern.
If both terms are different constructors, fail.

Injections
----------

If both terms are `inj`, and you are unifying `inj{s1, s}(p1)` and `inj{s2, s}(p2)`:

* If s1 < s2, decompose with `inj{s1, s2}(p1)` and `p2`.
* If s2 < s1, symmetric of above
* otherwise, fail

If one term is `inj` and the other is a constructor, fail.

Overloading
-----------
If one term is an overloaded symbol and the other is a constructor, fail.
If both terms are different overloaded symbols, fail.
If one term is `inj{s1, s2}(p1)` where p1 is an overloaded symbol, and the other is `p2`, an overload of `p1`, coerce to the least upper bound of p1 and p2 and decompose.
Otherwise if one is an injection and the other is an overloaded symbol, fail.

Map
---

If both patterns are of a map sort, we first normalize each map by categorizing each subterm according to one of three categories:

1. Elements
2. Variables
3. Functions (other than `.Map`, `_Map_`, and `|->`)

This process may yield the value \bottom for either map, in which case, fail.

First, we remove all subterms present in both maps from each map.

We then consider 4 cases:

1. Neither map has any variables or functions. In this case, invoke AC unification with the two maps.
2. One map has no functions, a single variable, and one or more elements, and the other map has no variables or functions.  In this case, invoke AC unification with the two maps.
3. One map has no elements or functions and one variable, and the other map has no functions or variables. In this case, invoke AC decomposition with the variable and the map.
4. Otherwise, add the constraint that the two maps are equal.

### AC Unification 

First we handle the cases where one map is empty:

* If both maps are empty, discharge.
* Otherwise, if one map is empty, fail.

We now are left with an AC unification equation over 3 possible terms:

* Elements
* Map concatenation
* Variables

We know neither top term is a variable because of case 3 above.

We can thus represent this as the following equation: `_Map_(s1, ..., sn) = _Map_(t1, ..., tm)` for n, m > 0, where si and tj are either map elements or variables.

We proceed by replacing each unique map element u |-> v in the equation above with a fresh variable X, and decomposing with X and u |-> v, treating `|->` as a constructor. Afterwards, we create an **AC equation** corresponding to the replaced equation.

### AC Binding

If one term is a variable X and the other is `_Map_(s1, ..., sn)` for n > 0, where si is either a map element or a variable, we proceed by replacing each unique map element si with a fresh variable Y, and decompose with Y and si, treating `|->` as a constructor. Afterwards, if X is a free variable, bind it to the replaced equation and add X to the mgu. Otherwise, if X is bound to a variable, decompose with the binding of X and the replaced equation. Otherwise, decompose with `_Map_(s1, ..., sn)` and the binding of X.

### AC Subproblems

After the priority queue is empty, we are left with two AC subproblems (one for maps, and one for sets, as described below). We then solve each one according to the following algorithm, which either succeeds or fails and may add additional bindings.

First, we replace each variable with its binding in the mgu until this can no longer occur.

We are left with a system of equations P == s1 = s1' /\ ... /\ sp = sp' where each si and si' is of the form `_Map_(t1, ..., tk)` for some k where each ti is a variable. We define u1, ..., un to be the unique variables in the system of equations, and associate each ui an integer variable xi. We then convert P into the following system of linear Diophantine equations:

d(u1, t1=t1')x1 + ... + d(un, t1=t1')xn = 0
.
.
.
d(u1, tp = tp')x1 + ... + d(un, tp=tp')xn = 0

Where d(ui, ti = ti') is the number of occurrences of ui in ti minus the number of occurrences of ui in ti'.

We then compute the set of positive, non-null, minimal solutions of this system of equations, called S. For each solution sj = (d1, ..., dn) in this set, we associate a new term variable vj.
`
We then compute the set of all subsets {s1, ..., sq} of S. Each subset becomes a solution of P in the following way:

{ui = _Map_(v1^s1(i), ..., vq^sq(i) | i from 1 to n}

Set
---

Set unification proceeds identical to map unification except that we treat each set element as a map element from its value to ().

List
----

If both terms are function symbols of list sort, we conside 5 cases:

1. If one list is `_List_(l1, Var1)` and the other list is `_List_(l2, Var2)`, where l1 and l2 have no opaque terms, and len(l1) <= len(l2), for i = 1 to len(l1), decompose with the ith element of l1 and l2. Then, remove len(l1) elements from the start of l2 and decompose with Var1 and `_List_(l2, Var2)`
2. If one list is `_List_(Var1, l1)` and the other list is `_List_(Var2, l2)`, where l1 and l2 have no opaque terms, and len(l1) <= len(l2), for i = 1 to len(l1), decompose with the ith element of l1 and the len(l2) - len(l1) + ith element of l2. Then, remove len(l1) elements from the end of l2 and decompose with Var1 and `_List_(Var2, l2)`
3. If both lists have no opaque terms, and they have the same length, unify each element in sequence. If they have different lengths, fail.
4. If one list l1 has no opaque terms and the other is `_List_(l2, Var)`, and len(l2) <= len(l1), then for i = 1 to len(
l2), decompose with the ith element of l1 and l2. Then, remove len(l2) elements from the start of l1 and decompose with Var and l1. If len(l2) > len(l1), fail.
4. If one list l1 has no opaque terms and the other is `_List_(Var, l2)`, and len(l2) <= len(l1), then for i = 1 to len(l2), decompose with the ith element of l2 and the len(l1) - len(l2) + ith element of l1. Then, remove len(l2) elements from the end of l1 and decompose with Var and l1. If len(l2) > len(l1), fail.
5. Otherwise, add the constraint that the two lists are equal.

Fallback
--------

If no other cases apply to patterns p1 and p2, add the constraint \equals(p1, p2)
