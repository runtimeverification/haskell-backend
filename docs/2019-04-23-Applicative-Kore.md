# Applicative Kore

_Applicative matching mu-logic_ (AML) is the applicative/functional fragment of matching mu-logic. AML is unsorted. It has a simple syntax that consists of variables, constants, propositional connectives, FOL binders, fixpoint binders, and application. 

_Applicative Kore_ (AppKore) is the language to write AML theories. We call the existing Kore language for full ML as _FullKore_.

## AppKore parser

### Keywords

AppKore has the following keywords:

```
module import axiom symbol notation hooked-symbol hooked-notation endmodule
```

### Identifiers

_Identifiers_ in AppKore are used as the names of variables, constants, notations, and modules. 

```
<id> ::= ...   // The precise regular expression is to be defined.
               // Ideally, it should allow anything except those starting with a "#".
               // Some examples: X, X1, X2, X_1, _1, _2, ...
               //                x, x1, x2, x_1, Xx, XX, ...
               //                Int, Nat, List, plus, mult, ...
               //                \and, \or, \iff, \equals, \ceil, ...
               //                _+_, _plus_, Nat+Nat:Nat, ...
               //                "abc", "ABC", "\n", "\"", "", ...
               //                1, 2, -1, -2, 0, 0xF, ...
<sharp-id> ::= // "#", or "#" followed by <id> (no space between them)
```

_Remark._ There are some conventions in using identifiers. For example, module names are often all in capital letters; constants that represent _sorts_ are often capital in their first letters (such as _Nat, Int_); constants that represent _functions/predicates_ are often all in lower case (such as _plus, mult_). We can enforce these conventions and embed them into the syntax of AppKore, but for now, these are merely conventions. 

### Patterns

```
<atom-pattern> ::=
| <id>                // can mean either an element variable, 
                      // or a constant, or a notation (alias);
                      // this has to be decided later by the *verifier*
| <sharp-id>          // a set variable
| "\bottom"           // the bottom
| "(" <pattern> ")"   // parentheses used for grouping

<app-pattern> ::=
| <atom-pattern>
| <app-pattern> <atom-pattern> // a b c is parsed as ((a b) c)

<pattern> ::=
| "\implies" <atom-pattern> <atom-pattern>     // implication
| "\forall" <element-variable> <atom-pattern>  // FOL binders
| "\mu" <set-variable> <atom-pattern>          // fixpoint binders

<element-variable> ::= <id>
<set-variable>     ::= <sharp-id>
```

Some examples:

```
\implies a        ... ... not wellformed: too few arguments
\implies a b      ... ... wellformed
\implies a b c    ... ... not wellformed: too many arguments
\implies (a b) c  ... ... wellformed
```

### Sentences and modules

An AppKore module consisting of a sequence of _sentences_. _Import sentence_ imports a module; _symbol sentence_ declares a constant symbol; _notation sentence_ declares a notation (a.k.a. alias); _axiom sentence_ specifies a pattern as an axiom of the module; a _hooked symbol sentence_ declares a constant symbol whose semantics is not given by the axioms, but given by the implementation; a _hooked notation sentence_ declares a notation whose definition is not given in the declaration, but given by the implementation. 

Each sentence/module is associated with zero, one, or more _attributes_. Attributes provide information and hints for the backends but cannot carry _additional_ semantic meaning. 

```
<sentence> ::=
| <import-sentence>
| <symbol-sentence>
| <notation-sentence>
| <axiom-sentence>
| <hooked-symbol-sentence>
| <hooked-notation-sentence>

<import-sentence> ::= "import" <id> <attribute>
<symbol-sentence> ::= "symbol" <id> <attribute>
<notation-sentence> ::= "notation" <id> <ids> "=" <pattern> <attribute>
<axiom-sentence> ::= "axiom" <pattern> <attribute>
<hooked-symbol-sentence> ::= "hooked-symbol" <id> <attribute>
<hooked-notation-sentence> ::= "hooked-notation" <id> <ids> <attribute>

<module> ::= "module" <id> <sentences> "endmodule" <attribute>

<ids> ::= "" | <id> | <id> <ids>
<attribute> ::= "[" "]" | "[" <id> <comma-ids> "]"
<comma-ids> ::= "" | "," <id> <comma-ids> 
<sentences> ::= "" | <sentence> <sentences>
```

## Some remarks on notations

AppKore allows the users to define notations (a.k.a. aliases). The __main principle of notations__ is that they can be desugared in a unique and well-founded way. Notations differ from symbols in many aspects, even though they share the same syntax in the AppKore grammar shown above. In the following, we illustrate some of the main differences between notations and symbols by examples. These differences will taken into consideration by no the parser, but the verifier, which we discuss later.

The purpose of this section is to show some examples of notations. 

#### Basic notations

A basic notation declaration has the following form:

```
notation foo X1 X2 ... Xn = P []
```

Here,  `foo` is the name of the notation; `n` is the _arity_ of `foo`; `X1`,...,`Xn` are _placeholders_ which may appear in pattern `P`. We require that `foo` does not appear in `P`; that is, we forbid recursive notation declarations. We require that `foo`,`X1`,...,`Xn` are all different identifiers. More of such _wellformedness conditions_ will be discussed in detail in the __AppKore Verifier__ section. 

As an example, _negation_ can be defined as a notation using implication and bottom, both of which are primitive logic constructs in AppKore. 

```
notation \neg P = \implies P \bottom []
```

Then, `\neg` is a notation that takes 2 arguments. Therefore:

```
\neg       ... ... not wellformed (captured by verifier, not parser) 
\neg a     ... ... wellformed
\neg a b   ... ... not wellformed (captured by verifier, not parser)
```

_Remark._ For most cases in practice, backends may not want to desugar notations but simply keep the notations as they are.

#### Notations with binders

As an example, consider the following notation declaration of the `exists`-binder defined in the usual way:

```
notation \exists X P = \neg (\forall X (\neg P)) [binder]
```

Here, `\exists` is the name of the notation, whose arity is 2. The two placeholders are `X` and `P`. In usual cases, placeholders are _metavariables over patterns_. However, in the above example, `X` is not a metavariable over patterns, but a _metavariable over element variables_. This can be told by analyzing the body of the declaration, `\neg (\forall X (\neg P))`. Since `X` occurs as the first argument of `\forall`, it must be of the nonterminal `<element-variable>`, and thus `X` ranges over element variables instead of all patterns. 

Another noticeable fact about `\exists` is its _binding behavior_; that is, it binds all free occurrences of the variable `X` in `P`. Binding behavior is important when using _substitution_, which is also defined as a notation and we will discuss about it later. In short, substitution is the so-called _capture-avoiding-substitution_, meaning that bound variables are renamed automatically to prevent unintended variable capture. The binding behavior of `\exists X P` means that its first argument `X` may be renamed in substitution. Finally, note that we put the `binder` attribute along with the declaration, so that the backends do not need to reverse engineer the information from the declaration. 

# ===== DO NOT REVIEW =====

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

```

## Parser and Verifier

It takes two process to fully parse an AppKore definition. The _parser_ simply parse the definition by the above grammar, without distinguishing element variables from symbols. After that, the _verifier_ reads the symbol declarations and figure out what are element variables and what are symbols. Those identifiers that have been declared as a symbol (see below) are symbols, and the rest identifiers are element variables. Note that set variables always start with a "#" so there is no chance to confuse them with the other identifiers.

_Verifier_ is also responsible for checking _notation definitions_, which we introduce below. Intuitively, all derived constructs are defined as notations (i.e., aliases), and the verifier should check that all notation definitions are _well-founded_ and any pattern written with notations can be unique desugared to a vanilla pattern without any notations/aliases in finitely many steps. All notations have correct number of arguments, etc.

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