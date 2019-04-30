# Applicative Kore

Applicative matching mu-logic (AML) is the fragment of matching mu-logic that contains only one universal sort for everything, one binary symbol called _application_, and some constants. 

Applicative Kore (AppKore) is a language that is used to write AML theories. We refer to the existing Kore for full ML as full Kore.

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

### Notation definition examples

The main principle of _notations_ (a.k.a., _aliases_) is that they must be able to translate/desugar to the primitive patterns in a unique way.

#### Basic notations

A (basic) notation definition has the following form:

```
notation foo X1 X2 ... Xn = <pattern>
```

where `foo` is a notation expecting `n` arguments where `n` is called its arity. Using this syntax, we can define many derived constructs in AppKore. For example,

```
notation \neg P = \implies P \bottom
```

By default, we keep the notations instead of desugaring them immediately. 

#### (Left/right-)associative notations

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

#### Hooked notations

A more advanced example of notations is _substitution_. We want to define `\subst X P Q` as a notation that represents the pattern obtained by substituting all free occurrences of `X` in `P` for `Q`, where alpha-renaming happens explicitly to prevent variable capturing. However, substitution is _different_ from the other notations that we have seen in previous sections. It is impossible to define it _in the logic_. (TODO:: Say why). However, it is also necessary in defining other common notations, such as the greatest fixpoint binder `\nu`, the dual of `\mu`. 

Our solution is to allow _hooked notations_. Hooked notations are notations _without explicit definitions_. Instead, _backends_ of AppKore must provide implementation of these notations. As example, `\subst` can be defined as follows:

```
hooked-notation \subst X P Q [required, desugar]
```

What the declaration says is that `\subst` expects three arguments, and the precise definition of `\subst` is given by AppKore backends, which is _required_. The attribute `desugar` specifies that `\subst` always desugars to its definitions. 

Hooked notations can be used to define many important notations that cannot be properly defined _in the logic_. 

#### Sentences

```
<sentence> ::=
| <import-sentence>
| <symbol-sentence>
| <hooked-symbol-sentence>
| <notation-sentence>
| <assoc-notation-sentence>
| <hooked-notation-sentence>
| <axiom-sentence>

<import-sentence> ::= "import" <id> <attribute>
<symbol-sentence> ::= "symbol" <id> <attribute>
<hooked-symbol-sentence> ::= "hooked-symbol" <id> <attribute>
<notation-sentence> ::= "notation" <id> <ids> "=" <pattern> <attribute>
<assoc-notation-sentence> ::= 
| "left-assoc-notation" <id> <attribute>
| "right-assic-notation" <id> <attribute>
<hooked-notation-sentence> ::= "hooked-notation" <id> <ids> <attribute>
<axiom-sentence> ::= "axiom" <pattern>

<ids> ::= "" | <id> | <id> <ids>
<attribute> ::= "[" "]" | "[" <id> <comma-ids> "]"
<comma-ids> ::= "" | "," <id> <comma-ids> 
```

## Builtin AppKore definitions

### Basic derived constructs

```
module BASIC-DERIVED-CONSTRUCTS
  hooked-notation \subst X P Q                                  [required, desugar]
  notation \neg P = \implies P \bot                             []
  notation \or P Q = \implies (\neg P) Q                        []
  left-assoc-notation \or                                       []
  notation \and P Q = \neg (\or (\neg P) (\neg Q))              []
  left-assoc-notation \and                                      []
  notation \iff P Q = \and (\implies P Q) (\implies Q P)        []
  notation \top = \neg \bot                                     []
  notation \exists X P = \neg \forall X \neg P                  []
  notation \nu X P = \neg \mu X (\neg (\subst X (\neg X) P))    []
  right-assoc-notation \forall                                  []
  right-assoc-notation \exists                                  []
  right-assoc-notation \mu                                      []
  right-assoc-notation \nu                                      []
endmodule
```

### Definedness

```
module DEFINEDNESS
  import BASIC-DERIVED-CONSTRUCTS                             []
  symbol \ceil                                                []
  axiom \ceil X                                               []
  notation \floor P = \neg (\ceil \neg P)                     []
  notation \member x P = \ceil (\and x P)                     []
  notation \equals P Q = \floor (\iff P Q)                    []
  notation \subset P Q = \floor (\implies P Q)                []
endmodule
```

### Inhabitant

```module INHABITANT
module INHABITANT
  import DEFINEDNESS                                                  []
  symbol \Sort                                                        []
  symbol \inh                                                         []
  notation \typeof X S = \subset X (\inh S)                           []
  notation \forallIn X S P = \forall X (\implies (\typeof X S) P)     []
  notation \existsIn X S P = \exists X (\and (\typeof X S) P)         []
  notation \muIn X S P = \mu X (\and P (\inh S))                      []
  notation \nuIn X S P = \nu X (\and P (\inh S))                      []
endmodule
```

## Translation from FullKore to AppKore (DO NOT REVIEW)
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

## 