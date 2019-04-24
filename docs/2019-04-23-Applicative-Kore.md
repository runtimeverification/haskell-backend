# Applicative Kore

Applicative matching mu-logic (AML) is the fragment of matching mu-logic that contains only one universal sort for everything, one binary symbol called _application_, and some constants. 

Applicative Kore (AppKore) is a language that is used to write AML theories. We refer to the existing Kore for full ML as full Kore.

## AppKore parser and unparser

The following two Haskell functions are needed:
```
unparse2 : HaskellKore -> ApplicativeKore
parse2   : ApplicativeKore -> HaskellKore
```
Using these two functions, we can translate any full Kore definitions to applicative Kore definitions by the following translation function:
```
tr : FullKore -> ApplicativeKore
tr(def.fullkore) = unparse2(parse(def.fullkore))
```
We require that `unparse2` and `parse2` satisfy the following property:
```
parse(def.fullkore) = parse2(tr(def.fullkore))
```

## AppKore syntax

### Primitive patterns

```
<primitive-pattern> ::=
| <element-variable>    // lowercase x, y, x1, x', var
| <set-variable>        // uppercase X, Y, X1, X', VAR
| <constant>            // any identifiers (ambiguity?)
| "\bottom"
| "\implies" <primitive-pattern> <primitive-pattern>   // right associative
| "\forall" <element-variable> <primitive-pattern>     // scope goes far right
| "\mu" <set-variable> <primitive-pattern>             // scope goes far right
| <primitive-pattern> <primitive-pattern>              // left associative
| "(" <primitive-pattern> ")"
```

### Patterns

```
<pattern> ::=
| <primitive-pattern>
| "\subst" <pattern> <pattern> <element-variable>  // substitution
| "\subst" <pattern> <pattern> <set-variable>      // substitution
| (extended with alias definitions)                // see below
```

### Basic derived constructs

```
module BASIC-DERIVED-CONSTRUCTS
  alias \neg P = \implies P \bot                             [basic]
  alias \or2 P Q = \implies (\neg P) Q                       [basic]
  alias \and2 P Q = \neg (\or (\neg P) (\neg Q))             [basic]
  alias \iff P Q = \and (\implies P Q) (\implies Q P)        [basic]
  alias \top = \neg \bot                                     [basic]
  alias \exists x P = \neg \forall x \neg P                  [basic]
  alias \nu X P = \neg \mu X (\neg (\subst P (\neg X) X))    [basic]
  alias \and P Q ... = \and2 P (\and Q ...)                  [basic]
  alias \or P Q ... = \or2 P (\or Q ...)                     [basic]
endmodule
```

### Definedness

```
module DEFINEDNESS
  import BASIC-DERIVED-CONSTRUCTS
  const \ceil                                                 [definedness]
  axiom \ceil x                                               [definedness]
  alias \floor P = \neg (\ceil \neg P)                        [definedness]
  alias \member x P = \ceil (\and x P)                        [definedness]
  alias \equals P Q = \floor (\iff P Q)                       [definedness]
  alias \subset P Q = \floor (\implies P Q)                   [definedness]
endmodule
```

### Inhabitant

```
module INHABITANT
  import DEFINEDNESS
  const \inh
  alias \typeof P Q = \subset P (\inh Q)
  alias \forall x : S . P = \forall x . \implies (\typeof x S) P
  alias \exists x : S . P = \exists x . \and (\typeof x S) P
endmodule
```



### Builtin construct (DO NOT REVIEW)

```
<builtin-construct-0> ::=
| "\bot"
| "\top"
<builtin-construct-1> ::=
| "\neg"
| "\forall" <element-binders>
| "\exists" <element-binders>
| "\mu" <set-binders>
| "\nu" <set-binders
| "\ceil"
| "\floor"
<builtin-construct-2> ::=
| "\implies"
| "\iff"
| "\equals"
| "\member"
| "\subset"
<builtin-construct-*> ::=
| "\and"
| "\or"

  /* function axioms */
  alias \fun0 F 
      = \exists z . \equals F z 
  alias \fun1 F 
      = \forall x1 . 
          \exists z . \equals (F x1) z
  alias \fun2 F 
      = \forall x1 . \forall x2 . 
          \exists z . \equals (F x1 x2) z

<element-binders> ::=
| <element-variable> "."
| <element-variable> "." <element-binders>
<set-binders> ::=
| <set-variable> "."
| <set-variable> "." <set-binders>
```



## Translation from full Kore to applicative Kore
**[Rule App-1].** Translating applications (with `>=1` argument patterns)

```
f{S1,...,Sk}(P1,...,Pn) => f P1 ... Pn

For example:
cons{S}(X:S,L:List{S}) => cons tr(X:S) tr(L:List{S})
cons{List{S}}(X:List{S},L:List{List{S}}) => cons tr(X:List{S}) tr(L:List{List{S}})
```

Intuitively, we can overload `cons` in applicative Kore and do not specify the sort parameters. The drawback of this rule is that the `parse2` is harder to implement as it needs to reverse engineer the sort parameters. Also, it requires that the return sort of `f` is fully determined by the sorts of its arguments. 

**[Rule App-0].** Translating applications (with no argument patterns)

```
f{S1,...,Sk}() => f S1 ... Sk
```

**[Rule EVar].**

```
X:S => x:S  // element variables are lower cases
```

**[Rule Propopositional].**

```
\and{S}(P,Q)     => \and P Q
\or{S}(P,Q)      => \or P Q
\implies{S}(P,Q) => \implies P Q
\iff{S}(P,Q)     => \iff P Q
\not{S}(P)       => \not_ S P
```

**[Rule Quantifier].**

```
\exists{S,R}(X:S,P) => \exists X:S P
\forall{S,R}(X:S,P) => \forall X:S P
```

**[Rule Ceil/Floor].**

```
\ceil{S,R}(P)  => \ceil P
\floor{S,R}(P) => \floor P
```

**[Rule Next/Rewrite].**

```
\next{S}(P,Q)     => \next P Q
\rewrites{S}(P,Q) => \rewrites P Q
```

**[Rule Equallity].**

```
\equals{S,R}(P,Q) => \equals P Q
```
