# Syntax of the Kore language

This documents describes the syntax of Kore, as admitted by the Haskell Backend.

## Lexical structure

### Comments

Kore allows C-style comments:

- `//` line comment
- `/*` block comment (non-nested) `*/`

Comments are considered whitespace.
The only lexical function of whitespace is to break the source text into tokens.

### String literals

```
<string-literal>
  ::= ['"'] <char>* ['"']

<char>
  ::= <escape-sequence>
    | <printable-ascii-char> except ['"', '\']

<printable-ascii-char>
  ::= U+0020 through U+007E
```

The following table summarizes the escape sequences allowed in string literals.
`h` stands for a single hexadecimal digit.
The surrogate code points in the range `[U+D800, U+DFFF]` are illegal in the Unicode escape sequences.
The UTF-32 code point must not exceed `U+10FFFF`.

<table>
<tr>
  <td>Escape sequence</td>
  <td>Decoding</td>
</tr>
<tr>
  <td><code>\t</code></td>
  <td>Horizontal tab (ASCII <code>HT</code>, Unicode <code>U+0009</code>)</td>
</tr>
<tr>
  <td><code>\n</code></td>
  <td>Line feed (ASCII <code>LF</code>, Unicode <code>U+000A</code>)</td>
</tr>
<tr>
  <td><code>\f</code></td>
  <td>Form feed (ASCII <code>FF</code>, Unicode <code>U+000C</code>)</td>
</tr>
<tr>
  <td><code>\r</code></td>
  <td>Carriage return (ASCII <code>CR</code>, Unicode <code>U+000D</code>)</td>
</tr>
<tr>
  <td><code>\"</code></td>
  <td>Double quote (ASCII <code>"</code>, Unicode <code>U+0022</code>)</td>
</tr>
<tr>
  <td><code>\\</code></td>
  <td>Backslash (ASCII <code>\</code>, Unicode <code>U+005C</code>)</td>
</tr>
<tr>
  <td><code>\xhh</code></td>
  <td>8-bit character (Unicode <code>U+00hh</code>)</td>
</tr>
<tr>
  <td><code>\uhhhh</code></td>
  <td>UTF-16 code point (Unicode <code>U+hhhh</code>)</td>
</tr>
<tr>
  <td><code>\Uhhhhhhhh</code></td>
  <td>UTF-32 code point (Unicode <code>U+hhhhhhhh</code>)</td>
</tr>
</table>

### Keywords

```
<keyword>
  ::= "module"  | "endmodule"
    | "import"
    | "sort"    | "hooked-sort"
    | "symbol"  | "hooked-symbol"
    | "axiom"   | "claim"
    | "alias"   | "where"
```

### Identifiers

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

## Syntax

The syntax of Kore is defined here in [Backus-Naur form](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form),
augmented with the following meta-syntactic notations for brevity:

```
<[$item]-sep-by-[$separator]>
  ::= ""
    | <[$item]-sep-by-1-[$separator]>

<[$item]-sep-by-1-[$separator]>
  ::= $item
    | $item $separator <[$item]-sep-by-1-[$separator]>
```

### Sorts

A sort is either a _sort variable_ or a _sort constructor_ applied to a list of _sort parameters_.

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

### Patterns

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
    | "\and" "{" <sort> "}" "(" <patterns> ")"
    | "\or" "{" <sort> "}" "(" <patterns> ")"
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
    // Syntactic sugar
    | "\left-assoc" "{" "}" "(" <application-pattern> ")"
    | "\right-assoc" "{" "}" "(" <application-pattern> ")"
```

The `left-assoc` (resp. `right-assoc`) construct allows a chain of applications of
left associative (resp. right associative) binary symbols to be flattened.
For example, `foo(foo(P1, P2), P3)` can be represented as
`\left-assoc(foo(P1, P2, P3))`.

### Attributes

Attributes are hints to the backend, often collected by the frontend.
Some attributes express syntactic information,
while others express semantic information.
All semantic information contained in attributes should correspond to axioms declared explicitly.
The hints indicate when the backend may use faster algorithms, more efficent data structures, and so on.
The meaning of particular attributes is implementation-defined.
The order of attributes is _never_ significant.

```
<attribute>
  ::= <application-pattern>

<attributes>
  ::= <[attribute]-sep-by-[","]>
```

### Sentences

A sentence is a single declaration.
Sentences always appear inside modules, defined below.

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
  ::= "hooked-sort" <sort-identifier> "{" <sort-variables> "}" "[" <attributes> "]"

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
<symbol-or-alias> ::= <symbol-identifier> "{" <sort-variables> "}"
```

### Definition, modules

A definition is a non-empty sequence of modules.

```
<definition>
  ::= "[" <attributes> "]" <modules>

<module>
  ::= "module" <module-name> <sentences> "endmodule" "[" <attributes> "]"

<modules>
  :: <[module]-sep-by-1-[whitespace]>
```

## Validity

A valid Kore definition conforms to the grammar of `<definition>` described above and the following conditions:

1.  In any sentence,
    a. every sort variable used in the sentence appears in the sort variable list;
    b. the sort variable list contains only distinct sort variable names (without duplicates).
2.  In any symbol or alias sentence,
    a. the sort parameters of the declared symbol or alias are distinct sort variables;
    b. the argument and result sorts have declarations in scope.
3.  Every sort, symbol, and alias must have a unique (in the definition) name. No sort, symbol, or alias may be declared more than once. Names may not be shared between categories; i.e. the same name may not be used for a sort and a symbol.
4.  In any alias sentence,
    a. the variables on the left-hand side are distinct, and
    b. their number and sorts agrees with the declaration of the alias;
    c. the pattern is valid and its sort agrees with the declared result sort;
    d. the pattern contains no free variables other than the declared variables.
5.  Module names are unique.
6.  In any import sentence,
    a. the imported module appears earlier in the definition, i.e. the modules in the definition are topologically sorted;
    b. the sentence appears before any non-import declarations in the module.

A declaration is in scope in a particular module if it appears in the module or if it is in scope (transitively) in any module imported by the module.
Within a module, the order of non-import sentences is not significant.

A valid Kore pattern conforms to the grammar of `<pattern>` described above and the following conditions:

1.  In any application pattern,
    a. the number of sort parameters to the symbol or alias agrees with its declaration;
    b. the number and sort of pattern arguments to the symbol or alias agrees with its declaration.
2.  In any occurrence of a sort, the number of sort parameters agrees with the declaration.
3.  All sorts, symbols, and aliases are declared before being used.
4.  In any matching logic pattern, the sort of pattern arguments agrees with the specified argument sort parameter.
5.  In any binder (quantifier or fixpoint), the sort of the variable argument agrees with its free occurrences in the pattern argument.
