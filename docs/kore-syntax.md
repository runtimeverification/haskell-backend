Syntax of the KORE language
===========================

This documents describes the syntax of KORE, as admitted by the Haskell Backend.

It is meant to be an easier to access source than the
[Semantics of K](docs/semantics-of-k.pdf)

Any change in the KORE Parser infrastructure should be reflected here.

Context-Free Syntax
-------------------

The definition below uses standard [BNF](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form).

Nevertheless, we use following notational convention for enumerations.
- enumeration symbols are plurals of the symbols they enumerate over.
  For example, `<attributes>` enumerates over `<attribute>`
- enumeration uses comma as a separator; enumeration symbols using
  whitespace as a separator are suffices with `_`, e.g., `<sentences_>`
- enumeration means zero, one, or more; enumeration symbols describing
  enumerations of one or more are suffixes with `+`, e.g. `<attributes+>`

These notations are just to assist the reader. All enumeration symbols are
properly defined at the end of this section.

### Definition, modules

```
<definition>
  ::= "[" <attributes> "]" <modules_+>

<attribute>
  ::= <application-pattern>

<module>
  ::=   "module" <module-name-id>
            <sentences_>
        "endmodule"
        "[" <attributes> "]"
```

### Sentences

```
<sentence>
  ::= <import-statement>
    | <sort-definition>
    | <hooked-sort-definition>
    | <symbol-definition>
    | <hooked-symbol-definition>
    | <axiom>
    | <claim>
    | <alias-definition>

<import-statement>
  ::= "import" <module-name-id>
        "[" <attributes> "]"

<sort-definition>
  ::= "sort" <sort-id> "{" <sort-variables> "}"
        "[" <attributes> "]"
<hooked-sort-definition>
  ::= "hooked-sort" <sort-id> "{" <sort-variables> "}"
        "[" <attributes> "]"

<symbol-definition>
  ::= "symbol" <symbol> "(" <sorts> ")" ":" <sort>
        "[" <attributes> "]"
<hooked-symbol-definition>
  ::= "hooked-symbol" <symbol> "(" <sorts> ")" ":" <sort>
        "[" <attributes> "]"

<alias-definition>
  ::= "alias" <alias> "(" <sorts> ")" ":" <sort>
        "where" <application-pattern> ":=" <pattern>
        "[" <attributes> "]"

<axiom>
  ::= "axiom" "{" <sort-variables> "}"
        <pattern>
        "[" <attributes> "]"
<claim>
  ::= "claim" "{" <sort-variables> "}"
        <pattern>
        "[" <attributes> "]"

<alias> ::= <symbol-or-alias>
<symbol> ::= <symbol-or-alias>
<symbol-or-alias> ::= <symbol-id> "{" <sort-variables> "}"

<sort-variable>
  ::= <sort-id>

<sort>
  ::= <sort-variable>
    | <sort-id> "{" <sorts> "}"
```

### Patterns

```
<pattern>
  ::= <element-variable>
    | <set-variable>
    | <ML-pattern>
    | <application-pattern>
    | <string-literal>

<variable>
  ::= <element-variable>
    | <set-variable>
<element-variable>
  ::= <element-variable-id> ":" <sort>
<set-variable>
  ::= <set-variable-id> ":" <sort>

<application-pattern> ::=
    <symbol-id> "{" <sorts> "}" "(" <patterns> ")"

<ML-pattern>
  ::=
    // Predicate Logic Connectives
      "\top" "{" <sort> "}" "(" ")"
    | "\bottom" "{" <sort> "}" "(" ")"
    | "\not" "{" <sort> "}"
        "(" <pattern> ")"
    | "\and" "{" <sort> "}"
        "(" <pattern> "," <pattern> ")"
    | "\or" "{" <sort> "}"
        "(" <pattern> "," <pattern> ")"
    | "\implies" "{" <sort> "}"
        "(" <pattern> "," <pattern> ")"
    | "\iff" "{" <sort> "}"
        "(" <pattern> "," <pattern> ")"
    // FOL quantifiers
    | "\exists" "{" <sort> "}"
        "(" <element-variable> "," <pattern> ")"
    | "\forall" "{" <sort> "}"
        "(" <element-variable> "," <pattern> ")"
    // Fixpoint operators
    | "\mu" "{" <sort> "}"
        "(" <set-variable> "," <pattern> ")"
    | "\nu" "{" <sort> "}"
        "(" <set-variable> "," <pattern> ")"
    // Definedness and totality
    | "\ceil" "{" <sort> "," <sort> "}"
        "(" <pattern> ")"
    | "\floor" "{" <sort> "," <sort> "}"
        "(" <pattern> ")"
    // Equality and membership
    | "\equals" "{" <sort> "," <sort> "}"
        "(" <pattern> "," <pattern> ")"
    | "\in" "{" <sort> "," <sort> "}"
        "(" <pattern> "," <pattern> ")"
    // Transition systems
    | "\next" "{" <sort> "}"
        "(" <pattern> ")"
    | "\rewrites" "{" <sort> "}"
        "(" <pattern> "," <pattern> ")"
    // Domain values
    | "\dv" "{" <sort> "}"
        "(" <string-literal> ")"
```

String literals are defined in the [Lexical Syntax](#lexical-syntax) section
below.

### Enumerations

```
<modules_+>
  ::= <module>
    | <module> <modules_+>

<sentences_>
  ::= ""
    | <sentence> <sentences_>

<patterns>
  ::= ""
    | <patterns+>
<patterns+>
  ::= <pattern>
    | <pattern> "," <patterns+>

<sorts>
  ::= ""
    | <sorts+>
<sorts+>
  ::= <sort>
    | <sort> "," <sorts+>

<sort-variables>
  ::= ""
    | <sort-variables+>
<sort-variables+>
  ::= <sort-variable>
    | <sort-variable> "," <sort-variables+>

<attributes>
  ::= ""
    | <attributes+>
<attributes+>
  ::= <attribute>
    | <attribute> "," <attributes+>

```

Lexical Syntax
--------------

In this section we use a mixture of BNF and regular expressions.

- `*` represents iteration, `|` represents union (disjunction)
- characters are enclosed in single quotes and only present in
  productions in lists, enclosed in square brackets, e.g.,
  `['r', 'n']`
- a list of characters represents their union (disjunction)


### Comments

C-style comments:

- `//` line comment
- `/*` block comment (non-nested) `*/`

### String literals

```
<string-literal>
  ::= ['"'] <char>* ['"']

<char>
  ::= <escape-char>
    | <ascii-char> except ['"', '\']
    | <printable-char> except ['"', '\']

<ascii-char>
  ::= first 128 ASCII characters
<printable-char>
  ::= Unicode graphic characters

<escape-char>
  ::= ['\'] <escaped-char>

<escaped-char>
  ::= ['"', '\', 'f', 'n', 'r', 't']
    | ['x'] <hex-digit2>
    | ['u'] <hex-digit4>
    | ['U'] <hex-digit8>

<hex-digit>
  ::= ['0'..'9', 'A'..'F', 'a'..'f']
<hex-digit2>
  ::= <hex-digit> <hex-digit>
<hex-digit4>
  ::= <hex-digit2> <hex-digit2>
<hex-digit8>
  ::= <hex-digit4> <hex-digit4>
```

### KeyWords

```
Keywords
  ::= "module"  | "endmodule"       | "import"
    | "sort"    | "hooked-sort"
    | "symbol"  | "hooked-symbol"
    | "axiom"   | "claim"
    |" alias"   | "where
```

### Identifiers

```
<id-first-char>
  ::= ['A'..'Z', 'a'..'z']
<id-other-char>
  ::= ['0'..'9', '\'', '-']
<id-char>
  ::= <id-first-char>
    | <id-other-char>
<id>
  ::= <id-first-char> <id-char>*
<symbol-id>
  ::= ['\']?<id>
<element-variable-id>
  ::= <id>
<set-variable-id>
  ::= ['@'] <id>
<sort-id>
  ::= <id>
<module-name-id>
  ::= <id>
```

An identifier cannot be a keyword.

