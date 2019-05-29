# Applicative Kore

_Applicative matching mu-logic_ (AML) is the applicative/functional fragment of matching mu-logic. AML is unsorted. It has a simple syntax that consists of variables, constants, propositional connectives, FOL binders, fixpoint binders, and application. 

_Applicative Kore_ (AppKore) is the language to write AML theories. We call the existing Kore language for full ML as _FullKore_.

AppKore/AML differs from FullKore/ML in two ways. Firstly, AppKore has a simpler syntax. It is unsorted and only contains constant symbols. Secondly, AppKore has support for fixpoint reasoning. This makes it capable of precisely capturing many mathematical domains, such as natural numbers, which FullKore/ML cannot.

## AppKore parser

### Keywords

AppKore has the following keywords:

```
module import axiom symbol notation meta-notation endmodule
```

Compared with FullKore/ML, we made three changes on the choice of keywords. 

Firstly, we remove `sort` and `hooked-sort`, because sorts in FullKore can be captured as (constant) symbols in AppKore. 

Secondly, we remove hooked sorts/symbols, because many mathematical domains (such as natural numbers) that cannot be captured in ML (without support for fixpoints) or FullKore can now be precisely captured in AppKore/AML. In other words, we can precisely capture the semantics of these "hooked" sorts/symbols by writing sufficient axioms in AML, instead of leaving it to backends and implementation. Note that backends and implementation still can and should hook these sorts/symbols and have builtin support for them. These "hooking" information will be declared as attributes. What is different from FullKore is that the way backends implement these hooked sorts/symbols does not affect the semantics, because they are completely axiomatized in AML.

Thirdly, we add `notation` and `meta-notation`. `notation` is a replacement of `alias` in FullKore. `meta-notation` is like `notation` but it declares meta-level notations such as capture-avoiding-substitution, whose precisely definition only exists on paper and cannot be formalized in AML. Mostly we only use `notation` in practice. `meta-notation` is rarely used.

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

#### Main principle of notations

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

#### Notations with `assoc` attribute

Some _binary notations_ are _associative_. One typical example is `\or`. It is inconvenient to write a disjunction of multiple patterns using the binary notation `\or`. Instead, we want to abbreviate `\or (\or (\or a b) c) d` as `\or a b c d`. This is achieved by using the `assoc` attribute in notation declarations. 

Specifically speaking, if `foo` is a binary notation, then we can use the `left-assoc` (or `right-assoc`) to specify that `foo` is left (or right) associative. Therefore,

|                   | [left-assoc]                  | [right-assoc]                 |
| ----------------- | ----------------------------- | ----------------------------- |
| `foo a1 a2`       | `foo a1 a2`                   | `foo a1 a2`                   |
| `foo a1 a2 a3`    | `foo (foo a1 a2) a3`          | `foo a1 (foo a2 a3)`          |
| `foo a1 a2 a3 a4` | `foo (foo (foo a1 a2) a3) a4` | `foo a1 (foo a2 (foo a3 a4))` |
| etc.              | etc.                          | etc.                          |

_Remark._ The attributes `left-assoc` and `right-assoc` do not carry semantic meaning. They carry only syntactic meaning. Specifically speaking, they tell the _verifier_ to accept patterns of the form `foo a1 a2 a3`, even if `foo` has been declared to have arity 2. Without these attributes, the verifier will reject the pattern `foo a1 a2 a3` because it is not wellformed.

As an example, here is the declaration of `\or` using `left-assoc` attribute:

```
notation \or P Q = \implies (\neg P) Q [left-assoc]
```

Another neat example is a variant of `\forall` and `\exists` that allows multiple binders:

```
notation \forall* X P = \forall X P [binder, right-assoc]
notation \exists* X P = \exists X P [binder, right-assoc]
```

Here, the `right-assoc` attribute tells the verifier to accept patterns of the form `\forall* X1 X2 ... Xn P` as a notation of the pattern `(\forall X1 ... (\forall Xn P) ...)`.

#### Meta-notations

Some notations are not definable in the logic. One such examples is _capture-avoiding substitution_. Specifically, we want to define `\subst X P Q` as a notation that represents the pattern obtained by substituting all free occurrences of `X` in `P` for `Q`, where alpha-renaming happens explicitly to prevent unintended variable capturing. 

We call such notations whose definitions cannot be formalized in AML _meta-notations_. Meta-notations are necessary in practice. The most important meta-notation is capture-avoiding-substitution, `\subst`, which is declared as a meta-notation as follows:

```
meta-notation \subst X P Q [required, desugar]
```

What the declaration says is that `\subst` expects three arguments, and the precise definition of `\subst` is given by the backends. All backends must provide an appropriate implementation of `\subst` as specified by the `[required]` attribute. The attribute `desugar` specifies that `\subst` should always be desugared (during runtime).

## Builtin modules

We present some builtin modules. There modules define all the basic derived constructs in AML. They will be implicitly imported by all AppKore modules.

### Basic derived constructs

```
module BASIC-DERIVED-CONSTRUCTS
  meta-notation \subst X P Q                                    [required, desugar]
  notation \neg P = \implies P \bot                             []
  notation \or P Q = \implies (\neg P) Q                        [left-assoc]
  notation \and P Q = \neg (\or (\neg P) (\neg Q))              [left-assoc]
  notation \iff P Q = \and (\implies P Q) (\implies Q P)        []
  notation \top = \neg \bot                                     []
  notation \exists X P = \neg \forall X \neg P                  [binder]
  notation \forall* X P = \forall X P                           [binder, right-assoc]
  notation \exists* X P = \exists X P                           [binder, right-assoc]
  notation \nu X P = \neg \mu X (\neg (\subst X (\neg X) P))    [binder]
  notation \mu* X P = \mu X P                                   [binder, right-assoc]
  notation \nu* X P = \nu X P                                   [binder, right-assoc]
endmodule
```

___QUESTION.___ Suppose we want to write `\iff a b c` as a notation of `\and (\iff a b) (\iff b c)`, what should we do?

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
  notation \forallIn X S P = \forall X (\implies (\typeof X S) P)     [binder]
  notation \existsIn X S P = \exists X (\and (\typeof X S) P)         [binder]
  notation \muIn X S P = \mu X (\and P (\inh S))                      [binder]
  notation \nuIn X S P = \nu X (\and P (\inh S))                      [binder]
endmodule
```

## AppKore verifier

It takes two processes to fully parse an AppKore module. The _parser_ simply parses it following the grammar. Note that the grammar does not distinguish element variables from symbols and notations. Therefore, we need the second process, where a _verifier_ analyzes the module and figures out which are element variables, which are symbols, and which are notations. In addition, the verifier checks if the module is wellformed. 

#### Identifier analysis

In the grammar of AppKore, we use identifiers for element variables, symbols, and notations. The parser does not distinguish them. The verifier needs to. This process is called _identifier analysis_. 

Process `Identifier Analysis` is:

1. If an identifier `id` has been declared as a symbol (or a hooked symbol) in the current module, or a module that is imported by the current module, then `id` is a symbol (or a hooked symbol); 
2. If an identifier `id` has been declared as a notation (or a hooked notation) in the current module, or a module that is imported by the current module, then `id` is a notation (or a hooked notation);
3. Otherwise, `id` is an element variable.

We use the term _current scope_ to mean the current module or a module that is imported by the current module.

#### Wellformedness conditions about (hooked) notations

In a notation declaration `notation foo X1 ... Xn = P [...]` or a hooked notation declaration `hooked-notation foo X1 ... Xn [...]`,  we require that:

1. `foo,X1,...,Xn` are distinct identifiers;
2. `foo` has not been declared in the current scope;
3. `P` doesn't contain `foo` (for notations);
4. `P` doesn't contain free variables (except placeholders `X1,...,Xn`) (for notations);
5. If `left-assoc` or `right-assoc` is one of the attributes, then `n` is 2;
6. `left-assoc` and `right-assoc` cannot both be attributes;

In a module, we require that:

1. There is no cyclic (hooked) notation declarations;

#### Wellformedness conditions about patterns

We require that:

1. All notations have the right number of arguments;

#### Wellformedness conditions about modules

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
