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

### Keywords

```
module import axiom symbol endmodule
notation assoc assoc-left assoc-right
```

### Identifiers

```
<id> ::= ...   // TBD. Ideally, it should allow anything except those starting with a #.
               // For example, X, X1, X2, X_1, _1, _2, ...
               //              x, x1, x2, x_1, Xx, XX, ...
               //              Int, Nat, List, plus, mult, ...
               //              \and, \or, \iff, \equals, \ceil, ...
               //              _+_, _plus_, Nat+Nat:Nat, ...
               //              "abc", "ABC", "\n", "\"", "", ...
               //              1, 2, -1, -2, 0, 0xF, ...
<sharp-id> ::= // "#", or "#" followed by <id> (no space between them)
```

### Patterns

```
<atom-pattern> ::=
| <id>        // can be either <element-variable> or <symbol>, decided by verifier
| <sharp-id>  // <set-variable>
| "\bottom"
| "(" <pattern> ")"

<app-pattern> ::=
| <atom-pattern>
| <app-pattern> <atom-pattern> // i.e., application is right associative

<pattern> ::=
| "\implies" <atom-pattern> <atom-pattern>
| "\forall" <element-variable> <atom-pattern>
| "\mu" <set-variable> <atom-pattern>
```

Some examples:

```
\implies a        ... ... not wellformed; not enough argument
\implies a b      ... ... wellformed
\implies a b c    ... ... not wellformed; too many arguments
\implies (a b) c  ... ... wellformed; (a b) is an application
```

It takes two process to fully parse an AppKore definition. The _parser_ simply parse the definition by the above grammar, without distinguishing element variables from symbols. After that, the _verifier_ reads the symbol declarations and figure out what are element variables and what are symbols. Those identifiers that have been declared as a symbol (see below) are symbols, and the rest identifiers are element variables. Note that set variables always start with a "#" so there is no chance to confuse them with the other identifiers.

_Verifier_ is also responsible for checking _notation definitions_, which we introduce below. Intuitively, all derived constructs are defined as notations (i.e., aliases), and the verifier should check that all notation definitions are _well-founded_ and any pattern written with notations can be unique desugared to a vanilla pattern without any notations/aliases in finitely many steps. All notations have correct number of arguments, etc.

### Notation definitions

A (basic) notation definition has the following form:

```
notation foo X1 X2 ... Xn = <pattern>
```

where `foo` is a notation expecting `n` arguments where `n` is called its arity. Using this syntax, we can define many derived constructs in AppKore. For example,

```
notation \neg P = \implies P \bottom
```

By default, we keep the notations instead of desugaring them immediately. 

Sometimes, it is convenient to define _volatile notations_ with an arbitrarily number of arguments. For example, `\or P1 P2 ... Pn` for any `n >= 2`. We achieve this by defining a binary notation `\or P Q` and specify that this notation is _(left/right-)associative_. 

```
notation \or P Q = \implies (\neg P) Q
left-assoc-notation \or
```

The line `left-assoc-notation \or` tells the verifier to accept patterns of the form `\or P1 P2 ... Pn`, and desugar it (if required), uniquely, to `(\or ... (\or P1 P2) ... Pn)`. Note that there is nothing related to the semantics; it is merely a notation about the syntax.

Similarly, we can define volatile `\and` as

```
notation \and P Q = \neg (\or (\neg P) (\neg Q))
left-assoc-notation \and
```

Volatile `\forall` can be defined as

```
right-assoc-notation \forall
```

which tells the verifier to accept patterns of the form `\forall X1 X2 ... Xn P` and desugar it (if required), uniquely, to `(\forall X1 ... (\forall Xn P) ...)`.



```
notation \neg P = \implies P \bot                             [basic]
notation \iff P Q = \and (\implies P Q) (\implies Q P)        [basic]
notation \top = \neg \bot                                     [basic]
notation \exists x P = \neg \forall x \neg P                  [basic]
notation \nu X P = \neg \mu X (\neg (\subst P (\neg X) X))    [basic]
notation \and P Q ... = \and2 P (\and Q ...)                  [basic]
notation \or P Q ... = \or2 P (\or Q ...)                     [basic]
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
