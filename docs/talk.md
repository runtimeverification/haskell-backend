# The Kore Language
*The Kore language is an intermediate language that links frontends and backends.*
Suppose in frontends we have a K definition "imp.k":
```
  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  ... ...
  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
  ... ...
```
It is tranformed to a Kore definition "imp.kore", in which all syntactic sugar and semantics attributes in "imp.k" are desugared and defined in terms of matching logic axioms:
```
  sort Int
  sort Id
  sort AExp
  symbol plusAExp(AExp, AExp) : AExp
  axiom{S, R} /* The strictness axiom of plusAExp */
              /* Don't worry about the details for now */
  \implies{R}(
    \equals{KSort, R}(KgetSort(C:KPattern{}), Ctxt{S, AExp}),  
    \equals{AExp, R}(plusAExp{}(ctxtapp{S,AExp}(C:KPattern{}, X:S), E:AExp),
                     ctxtapp{S,AExp}(
                       \exists{S,AExp}(
                         HOLE:S, 
                         gamma0{S,AExp}(
                           HOLE:S, 
                           plusAExp{}(ctxtapp{S,AExp}(C:KPattern{}, HOLE:S), E:AExp))), 
                       X:S)))
```

Semantics of K is given in terms of
 - Give a transformation from K definition to Kore definition
 - Give a syntax and semantics of Kore (close to finish)





*The Kore language is a way to define (infinite) matching logic theories in a finite amount of time and space.*
Why consider infinite theories? Because K definitions will be transformed to infinite theories.
 - [binder] ----> The theory of binders (e.g. the lambda calculus)
 - [strict] ----> The theory of contexts and rewriting
 - etc

Let's use lambda calculus as an example to see whether we need to deal with infinite theories.
*Lambda calculus as a matching logic theory*
```
sort Exp
symbol lambda0(Exp, Exp) : Exp
symbol app(Exp, Exp) : Exp
alias lambda(x, e) := \exists(x, lambda0(x, e))
axiom (Beta)
  app((lambda x . e), e') = e[e'/x], where e and e' are lambda terms.
```
The (Beta) axiom is an axiom schema, i.e., it is a shorthand for an infinite number of axioms. When it comes to a formal language (like Kore), we have issues:
 - We cannot afford enumerating an infinite number of axioms; We need a finite representation of it.
 - What does the substitution bracket "[\_/_]" mean?
 - What does "e and e' are lambda terms" mean (side conditions)?

**Kore is our best effort to design a language that allows us define infinite matching logic theories using a finite number of time and space, while as simple / human-readable as possible.**

To solve the above (and more) issues in a non-adhoc and unified way, we use *the meta-theory*. Refer to the K semantics proposal for theoretical details. Think of the *meta-theory* as the theory for abstract syntax trees of matching logic patterns and theories. Using the *meta-theory* allows us to define side conditions very easily:
```
axiom isLambdaTerm(Kvariable(..)) = true  /* variables are lambda terms */
axiom isLambdaTerm(Kapplication(app, (e, e'))) = isLambdaTerm(e) and isLambdaTerm(e') 
axiom isLambdaTerm(Kexists(x, Kapplication(lambda0, (x, P)))) = isLambdaTerm(P)
```

*Lifting from object-level to the meta-level (Parsing)*
```
/* [[_]] is called the lifting bracket */
[[X:Int]] = Kvariable("X", Ksort("Int"))
[[\and(P, Q)]] = Kand([[P]], [[Q]])
... ...
```

*Faithfulness of the meta-theory*
```
T |- P  iff meta-theory |- Kdeduce([[T]], [[P]])
```

**Kore is our best effort to design a language that allows us define infinite matching logic theories using a finite number of time and space, while as simple / human-readable as possible.**

*Kore supports Parametric sorts*
```
  sort   List{S}
  symbol nil{S}()            : List{S}
  symbol cons{S}(S, List{S}) : List{S}
```
