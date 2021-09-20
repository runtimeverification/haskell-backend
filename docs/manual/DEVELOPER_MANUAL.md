# Kore Manual

## Table of Contents

1. [Introduction](#introduction)
    1. [Motivation](#introduction-motivation)
    2. [Document Structure](#introduction-document-structure)
2. [Basics](#basics)
3. [Design](#design)
3. [Implementation](#implementation)
4. [Language](#language)
    1. [Lexical Structure](#language-lexical-structure)
        1. [Comments](#language-lexical-structure-comments)
        2. [String literals](#language-lexical-structure-string-literals)
        3. [Keywords](#language-lexical-structure-keywords)
        4. [Identifiers](#language-lexical-structure-identifiers)
    2. [Syntax](#language-syntax)
        1. [Sorts](#language-syntax-sorts)
        2. [Patterns](#language-syntax-patterns)
        3. [Attributes](#language-syntax-attributes)
        4. [Sentences](#language-syntax-sentences)
        5. [Definition and Modules](#language-syntax-definition-and-modules)
    3. [Validity](#language-validity)
5. [Commands](#commands)
6. [K Framework](#kframework)
7. [Application Notes](#application-notes)
8. [Glossary](#glossary)

## <span id="introduction">Introduction</span>

### <span id="introduction-motivation">Motivation</span>

### <span id="introduction-document-structure">Document Structure</span>

## <span id="basics">Basics</span>

## <span id="design">Design</span>

## <span id="implementation">Implementation</span>

## <span id="language">Language</span>

### <span id="language-lexical-structure">Lexical Structure</span>

#### <span id="language-lexical-structure-comments">Comments</span>

Kore allows C-style comments:

* `//` line comment
* `/*` block comment (non-nested) `*/`

#### <span id="language-lexical-structure-string-literals">String literals</span>

```
<string-literal>
  ::= ['"'] <char>* ['"']

<char>
  ::= <escape-sequence>
    | <printable-ascii-char> except ['"', '\']

<printable-ascii-char>
  ::= U+0020 through U+007E
```

The following table summarizes the escape sequences allowed in string literals. `h` stands for a single hexadecimal digit. The surrogate code points in the range `[U+D800, U+DFFF]` are illegal in the Unicode escape sequences. The UTF-32 code point must not exceed `U+10FFFF`.

TODO insert table

#### <span id="language-lexical-structure-keywords">Keywords</span>

```
<keyword>
  ::= "module"  | "endmodule"
    | "import"
    | "sort"    | "hooked-sort"
    | "symbol"  | "hooked-symbol"
    | "axiom"   | "claim"
    | "alias"   | "where"
```

#### <span id="language-lexical-structure-identifiers">Identifiers</span>

```
<identifier>
  ::= <identifier-first-char> <identifier-char>*

<identifier-char>
  ::= <identifier-first-char>
    | <identifier-other-char>

<identifier-first-char>
  ::= ['A'..'Z', 'a'..'z']

<identifier-other-char>
  ::= ['0'..'9', '\'', '-']

<symbol-identifier>
  ::= ['\']? <identifier>

<element-variable-identifier>
  ::= <identifier>

<set-variable-identifier>
  ::= ['@'] <identifier>

<sort-identifier>
  ::= <identifier>

<module-name>
  ::= <identifier>
```

Identifiers must not be `<keyword>`s.

### <span id="language-syntax">Syntax</span>

The syntax of Kore is defined here in [Backus-Naur form](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form), augmented with the following meta-syntactic notations for brevity:

```
<[$item]-sep-by-[$separator]>
  ::= ""
    | <[$item]-sep-by-1-[$separator]>

<[$item]-sep-by-1-[$separator]>
  ::= $item
    | $item $separator <[$item]-sep-by-1-[$separator]>

```

#### <span id="language-syntax-sorts">Sorts</span>

A sort is either a *sort variable* or a *sort constructor* applied to a list of *sort parameters*.

```
<sort>
  ::= <sort-variable>
    | <sort-identifier> "{" <sorts> "}"

<sorts>
  ::= <[sort]-sep-by-[","]>

<sort-variable>
  ::= <sort-identifier>

<sort-variables>
  ::= <[sort-variable]-sep-by-[","]>
```

#### <span id="language-syntax-patterns">Patterns</span>

```
<pattern>
  ::= <variable-pattern>
    | <matching-logic-pattern>
    | <application-pattern>
    | <string-literal>

<patterns>
  ::= <[pattern]-sep-by-[","]>

<variable-pattern>
  ::= <element-variable>
    | <set-variable>

<element-variable>
  ::= <element-variable-identifier> ":" <sort>

<set-variable>
  ::= <set-variable-identifier> ":" <sort>

<application-pattern> ::=
    <symbol-identifier> "{" <sorts> "}" "(" <patterns> ")"

<matching-logic-pattern>
  ::=
    // Connectives
      "\top" "{" <sort> "}" "(" ")"
    | "\bottom" "{" <sort> "}" "(" ")"
    | "\not" "{" <sort> "}" "(" <pattern> ")"
    | "\and" "{" <sort> "}" "(" <pattern> "," <pattern> ")"
    | "\or" "{" <sort> "}" "(" <pattern> "," <pattern> ")"
    | "\implies" "{" <sort> "}" "(" <pattern> "," <pattern> ")"
    | "\iff" "{" <sort> "}" "(" <pattern> "," <pattern> ")"
    // Quantifiers
    | "\exists" "{" <sort> "}" "(" <element-variable> "," <pattern> ")"
    | "\forall" "{" <sort> "}"
        "(" <element-variable> "," <pattern> ")"
    // Fixpoints
    | "\mu" "{" "}" "(" <set-variable> "," <pattern> ")"
    | "\nu" "{" "}" "(" <set-variable> "," <pattern> ")"
    // Predicates
    | "\ceil" "{" <sort> "," <sort> "}" "(" <pattern> ")"
    | "\floor" "{" <sort> "," <sort> "}" "(" <pattern> ")"
    | "\equals" "{" <sort> "," <sort> "}" "(" <pattern> "," <pattern> ")"
    | "\in" "{" <sort> "," <sort> "}" "(" <pattern> "," <pattern> ")"
    // Rewriting
    | "\next" "{" <sort> "}" "(" <pattern> ")"
    | "\rewrites" "{" <sort> "}" "(" <pattern> "," <pattern> ")"
    // Domain values
    | "\dv" "{" <sort> "}" "(" <string-literal> ")"
    // Syntax sugar
    | "\left-assoc" "{" "}" "(" <application-pattern> ")"
    | "\right-assoc" "{" "}" "(" <application-pattern> ")"
```

#### <span id="language-syntax-attributes">Attributes</span>

Attributes are hints to the backend, often collected by the frontend. Some attributes express syntactic information, while others express semantic information. All semantic information contained in attributes should correspond to axioms declared explicitly. The hints indicate when the backend may use faster algorithms, more efficient data structures, etc. (TODO be more specific). The meaning of particular attributes is implementation-defined. The order of attributes is **never** significant.

```
<attribute>
  ::= <application-pattern>

<attributes>
  ::= <[attribute]-sep-by-[","]>
```

#### <span id="language-syntax-sentences">Sentences</span>

A sentence is a single declaration. Sentences always appear inside modules, defined below.

```
<sentence>
  ::= <sentence-import>
    | <sentence-sort>
    | <sentence-hooked-sort>
    | <sentence-symbol>
    | <sentence-hooked-symbol>
    | <sentence-alias>
    | <sentence-axiom>
    | <sentence-claim>

<sentence-import>
  ::= "import" <module-name> "[" <attributes> "]"

<sentence-sort>
  ::= "sort" <sort-identifier> "{" <sort-variables> "}" "[" <attributes> "]"

<sentence-hooked-sort>
  ::= "hooked-sort" <sort-id> "{" <sort-variables> "}" "[" <attributes> "]"

<sentence-symbol>
  ::= "symbol" <symbol> "(" <sorts> ")" ":" <sort> "[" <attributes> "]"

<sentence-hooked-symbol>
  ::= "hooked-symbol" <symbol> "(" <sorts> ")" ":" <sort> "[" <attributes> "]"

<sentence-alias>
  ::= "alias" <alias> "(" <sorts> ")" ":" <sort> "where" <application-pattern> ":=" <pattern> "[" <attributes> "]"

<sentence-axiom>
  ::= "axiom" "{" <sort-variables> "}" <pattern> "[" <attributes> "]"

<sentence-claim>
  ::= "claim" "{" <sort-variables> "}" <pattern> "[" <attributes> "]"

<alias> ::= <symbol-or-alias>
<symbol> ::= <symbol-or-alias>
<symbol-or-alias> ::= <symbol-id> "{" <sort-variables> "}"
```

#### <span id="language-syntax-definition-and-modules">Definition and modules</span>

A definition is a non-empty sequence of modules.

```
<definition>
  ::= "[" <attributes> "]" <modules>

<module>
  ::= "module" <module-name> <sentences> "endmodule" "[" <attributes> "]"

<modules>
  :: <[module]-sep-by-1-[whitespace]>
```

### <span id="language-validity">Validity</span>

A valid Kore definition conforms to the grammar of `<definition>` described above and the following conditions:

1. In any sentence:
    1. every sort variable used in the sentence appears in the sort variable list
    2. the sort variable list contains only distinct sort variable names (without duplicates)
2. In any symbol or alias sentence:
    1. the sort parameters of the declared symbol or alias are distinct sort variables
    2. the argument and result sorts have declarations in scope
3. Every sort, symbol, and alias must have a unique (in the definition) name. No sort, symbol, or alias may be declared more than once. Names may not be shared between categories; i.e. the same name may not be used for a sort and a symbol.
4. In any alias sentence:
    1. the variables on the left-hand side are distinct
    2. their number and sorts agrees with the declaration of the alias
    3. the pattern is valid and its sort agrees with the declared result sort
    4. the pattern contains no free variables other than the declared variables
5. Module names are unique
6. In any import sentence:
    1. the imported module appears earlier in the definition, i.e. the modules in the definition are topologically sorted
    2. the sentence appears before any non-import declarations in the module

A declaration is in scope in a particular module if it appears in the module or if it is in scope (transitively) in any module imported by the module. (TODO I think this has changed). Within a module, the order of non-import sentences is not significant.

A valid Kkore pattern conforms to the grammar of `<pattern>` described above and the following conditions:

1. In any application pattern:
    1. the number of sort parameters to the symbol or alias agrees with its declaration
    2. the number and sort of pattern arguments to the symbol or alias agrees with its declaration
2. In any occurrence of a sort, the number of sort parameters agrees with the declaration.
3. All sorts, symbols, and aliases are declared before being used.
4. In any matching logic pattern, the sort of pattern arguments agrees with the specified argument sort parameter.
5. In any binder (quantifier or fixpoint), the sort of the variable argument agrees with its free occurrences in the pattern argument.

### <span id="language-implicit-sort-signatures">Implicit Sort Signatures</span>

#### <span id="language-implicit-sort-signatures-connectives">Connectives</span>

```
\top{S}() : S
\bottom{S}() : S
\not{S}(S) : S
\and{S}(S, S) : S
\or{S}(S, S) : S
\implies{S}(S, S) : S
\iff{S}(S, S) : S
```

#### <span id="language-implicit-sort-signatures-quantifiers">Quantifiers</span>

```
\exists{S}(x:T, S)
\forall{S}(x:T, S)
```

#### <span id="language-implicit-sort-signatures-fixpoints">Fixpoints</span>

```
\mu{}(@X:S, S) : S
\nu{}(@X:S, S) : S
```

#### <span id="language-implicit-sort-signatures-rewriting">Rewriting</span>

```
\next{S}(S) : S
\rewrites{S}(S, S) : S
```

#### <span id="language-implicit-sort-signatures-domain-values">Domain values</span>

```
\dv{S}(#String) : S
```

## <span id="commands">Commands</span>

## <span id="kframework">K Framework</span>

## <span id="application-notes">Application Notes</span>

## <span id="glossary">Glossary</span>

<span id="bmc">*BMC*</span>

  1. (noun, acronym) Bounded model checking. Execute the program on all paths for a given number of steps (a.k.a. bound), attempting to identify given properties (bugs, unexpected behaviours, etc.) in the execution graph.

<span id="constructor-like">*constructor-like*</span>

  1. (adjective) A pattern is *constructor-like* if logical equality is syntactic equality. A [pattern](#pattern) is constructor-like if it is logically equal (in the `\equals` sense) to another constructor-like pattern if and only if the patterns are syntactically equal. The constructor-like patterns of a sort comprise a normal form of elements in that sort.
  2. (adjective) A symbol is *constructor-like* if it may form the head of a constructor-like application pattern (in the sense defined about). Roughly, this means the symbol has injectivity and no-confusion axioms.

<span id="function">*function*</span>

  1. (noun) An application symbol that, when applied to [function-like](#function-like) patterns, produces function-like patterns.
  2. (noun/adjective) A [function-like](#function-like) pattern.

<span id="function-like">*function-like*</span>

  1. (adjective) A function-like [pattern](#pattern) can have at most one value, i.e. it satisfies $(\exists x . x = \varphi ) \vee \neg \lceil \varphi \rceil$.

<span id="functional">*functional*</span>

  1. (adjective) A functional [pattern](#pattern) has exactly one value, i.e. it satisfies $(\exists x . x = \varphi)$.

<span id="pattern">*pattern*</span>

  1. (noun) The internal representation of a syntactic element. It may have constructs which cannot be represented directly into syntactic elements (e.g. map domain values), but it is expected that it is possible to create an equivalent syntactic representation.

<span id="predicate">*predicate*</span>

  1. (noun) A [pattern](#pattern) that can evaluate only to top and bottom. Application patterns that can only evaluate to top and bottom are hard to identify (TODO Why?), so some of the code that identifies predicates fails on these (TODO clarify what code?). Whenever a [substitution](#substitution) can be extracted efficiently, the "predicate" term may refer to the non-substitution part of the predicate.

<span id="sbc">*SBC*</span>

  1. (noun, acronym) Semantics-based compilation. Compilation that uses the semantics of the language to analyze the behaviour of the program (e.g. through symbolic execution), and uses what it learned to improve the compilation result.

<span id="sort-injection">*sort injection*</span>

  1. (noun) A [symbol](#symbol) with the `sortInjection` attribute. The sort injection symbol is used to represent the K sub-sort relation in Kore. K sorts contain symbols and sorts (their sub-sorts), but Kore sorts contain only symbols. The sort injection symbol wraps patterns of a sub-sort so they can be included (*injected*) into the super-sort. Two important properties follow from this definition. First, sort injection symbols are injective. Second, the sort injection symbol from a particular sub-sort is distinct (in the no-confusion-different-constructors sense) from the super-sort's constructors.
  2. (noun) A sort injection is a [pattern](#pattern) of the form $inj\{Sub\{\}, Super\{\}\}(\varphi:Sub\{\})$ where `inj{Sub{}, Super{}}` is a sort injection symbol (described above). Where the K sort `Super` contains `Sub`, the pattern $\varphi$ with least-sort `Sub` can appear anywhere that a term of sort `Super` is required. In Kore, this is represented with the injection above because all sorts are regarded as distinct.

<span id="substitution">*substitution*</span>

  1. (noun) A [predicate](#predicate) of the form $x_1=\varphi_1 \land x_2=\varphi_2 \land \dots \land x_n=\varphi_n$ where $x_i$ are variables and $\varphi_i$ are patterns.

<span id="symbol">*symbol*</span>

  1. TODO

<span id="term-pattern">*term pattern*</span>

  1. (noun) A [pattern](#pattern) of a specific type. A term pattern is usually constructed with variables and function application patterns. In some cases, it is used for any pattern with the expectation that it will be reduced, as much as reasonably possible, to a variable-application form.
