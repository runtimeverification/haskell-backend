Unification modulo overloaded constructors
==========================================

Summary
-------

Proposal:

1. Annotate overloaded constructors with both `constructor` and `overloaded`
attributes
1. Simplify terms using the overloading axioms to push injections towards top
1. Solve most unification problems using regular constructor non-confusion
1. Handle (or not) special case of overloaded constructor vs. injection

Background
----------

K allows overloading of operators by associating the same label to multiple
productions.  Example (derived from the [K WASM semantics](https://github.com/kframework/wasm-semantics)):

```
    syntax IValType ::= "i32" | "i64"
    syntax FValType ::= "f32" | "f64"
    syntax AValType ::= IValType | FValType
    syntax Number ::= Int | Float
    syntax IVal ::= "<" IValType ">" Int    [klabel(<_>_)]
    syntax FVal ::= "<" FValType ">" Float  [klabel(<_>_)]
    syntax  Val ::= "<" AValType ">" Number [klabel(<_>_)]
                  | IVal | FVal
```

Here the `klabel` annotations allow for the `Val ::= "<" AValType ">" Number`
production to encompass both `IVal` and `FVal` productions and to be used to
construct terms referring to both of them (as well as to proper `Val`s).

This is K's way to deal with overloading.  An additional restriction imposed by
K implementations is that of __SingleOverloadPerSort__:

> Given sort `s` and label `l` there exists at most one production of result
sort `s` annotated with `klabel(l)`.

To capture the relation between these constructors, the K to KORE compilation
pipeline, while keeping the associated labels distinct, generates overloading
axioms of the form:

```
< inj{IValType, AValType}(IT:IValType) > inj{Int, Number}(I:Int)
  = inj{IVal,Val}(< IT:IValType > I:Int) 

< inj{FValType, AValType}(FT:FValType) > inj{Float, Number}(F:Float)
  = inj{FVal,Val}(< FT:FValType > F:Float) 
```

Problems
--------

Although overloading introduces a higher degree of modularization through
some form of subtype-polymorphism, it puts a higher burden over the
unification procedure.

1. Due to axioms like the above being generated, the overloaded constructors
are no longer proper constructors and therefore are not marked as such,
which hinders unification, given that usually the rules lhs is expected to be
constructor-based. This is especially bad because it also makes disproving of
unification harder and thus generates more (im)possible constrainted solutions.

2. Unification of these constructs needs to be performed modulo overloading
axioms like the ones above.

Proposed solution
-----------------

First observation is that although overloaded constructors are not proper
constructors, they behave as such in most instances: they are injective, so
no-confusion-same-constructor applies naturally, but also they are subject to
most no-confusion-different-constructors rules.  Indeed, due to the
__SingleOverloadPerSort__ constraint, the only confusion possible for an
oveloaded operation is that with an injection operation as given by the
overloading axioms.

Hence, the proposed solution for handling problem (1) specified above is to
annotate overloaded constructors with the `constructor` keyword, but also
add the `overload` keyword and check for it in the constructor-injection
unification part.

For the second problem, the issue comes from the fact that the unifying modulo
the overloading axioms might require applying them either way (left-to-right or
right-to-left).

### Example (why apply overloading axioms left-to-right)

One advantage of left-to-right application of overloading axioms is that it
helps computing the lowest sort for a term. For example, consider lists of
expressions overloaded by lists of values as in
[SIMPLE](https://github.com/kframework/k/blob/master/k-distribution/tutorial/2_languages/1_simple/1_untyped/simple-untyped.k):

```
  syntax Exps ::= List{Exp,","}          [strict]  // automatically hybrid now
  syntax Vals ::= List{Val,","}
```

Consider the definition of `Val`ues (including `lambda`), the syntax for
function call, and the function call rule itself:

```
  syntax Exp ::= Exp "(" Exps ")"        [strict]

  syntax Val ::= Int | Bool | String
               | array(Int,Int)
               | lambda(Ids,Stmt)
  syntax Exp ::= Val
  syntax Exps ::= Vals

  rule <k> lambda(Xs,S)(Vs:Vals) ~> K => mkDecls(Xs,Vs) S return; </k>
       <control>
         <fstack> .List => ListItem((Env,K,C)) ...</fstack>
         C
       </control>
       <env> Env => GEnv </env>
       <genv> GEnv </genv>
```

The rule above requires that the second argument of the application expression
(which should be a list of expressions, is actually a list of values). If
overloading axioms are applied left-to-right, the normalized term for, e.g.,

```
(1) inj{Int,Exp}(3), inj{Int,Exp}(7), inj{Val,Exp}(lambda(.Ids, skip)), .Exps
```

would be simplified to

```
inj{Vals, Exps}(inj{Int, Val}(3), inj{Int, Val}(7), lambda(.Ids, skip), .Vals)
```

which would alow it to be direcly matched by `inj{Vals, Exps}(Vs:Vals)`.

If the rules were to be applied from right to left, then the normalized term
would look as the expression (1) above, and it would be much harder to unify it
with `inj{Vals, Exps}(Vs:Vals)`.

### Unification cases

- overloaded constructor vs. same overloaded constructor: works the same as for
  other constructors, as overloaded constructors are injective
- overloaded constructor vs. different (overloaded) constructor: unification
  fails, similarly to the other constructors
- overloaded constructor vs. injection: 

  + if the injection part __is matched__ by any of the RHSs of the overloading
    axioms (it can be at most one), then we can apply the overloading axiom in
    reverse and use the same constructor case
  + otherwise, for now, throw an unsupported unification exception, as this
    would prevent increasing the number of variable and possible decompositions

