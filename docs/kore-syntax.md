Syntax of the KORE language
===========================

This documents describes the syntax of KORE, as admitted by the Haskell Backend.

It is meant to be an easier to access source than the
[Semantics of K](docs/semantics-of-k.pdf)

Any change in the KORE Parser infrastructure should be reflected here.

Lexical Syntax
--------------

### Comments

- C-style comments (non-nested)

### Strings

```
StringLiteral ::= "\"" {Char}* "\""

Char ::= EscapeChar || AsciiChar || PrintableChar

AsciiChar ::= first 128 ASCII characters
PrintableChar ::= printable according to the C++ iswprint function

EscapeChar
  ::= ['\"', '\\', '\f', '\n', '\r', '\t']
    | "\x" {HexDigit}2
    | "\u" {HexDigit}4
    | "\U" {HexDigit}8

HexDigit ::= ['0'..'9', 'A'..'F', 'a'..'f']
```

### KeyWords

```
Keywords = "module" | "endmodule" | "sort" | "symbol" | "alias" | "axiom"
```

### Identifiers

```
IdFirstChar ::= ['A'..'Z', 'a'..'z']
IdOtherChar ::= ['0'..'9', '\'', '-']
IdChar ::= IdFirstChar | IdOtherChar
GenericId ::= IdFirstChar {IdChar}*
SymbolId ::= {"\"}?GenericId
ElemVarId ::= GenericId
SetVarId ::= "@" GenericId
SortId ::= GenericId
ModuleNameId ::= GenericId
```

An identifier cannot be a keyword

Context-Free Syntax
-------------------

```
Definition ::= Attributes {Module}+

Attributes ::= "[" {Pattern ","}* "]"

Module ::= "module" ModuleNameId {Sentences}* "endmodule" Attributes

Sentence
  ::= ImportStatement
    | SortDefinition   | HookedSortDefinition
    | SymbolDefinition | HookedSymbolDefinition
    | AliasDefinition
    | Axiom
    | Claim

ImportStatement ::= "import" ModuleNameId Attributes

SortDefinition ::= "sort" SortId SortParameters Attributes
HookedSortDefinition ::= "hooked-sort" SortId SortParameters Attributes

SymbolDefinition ::=
    "symbol" SymbolId SortParameters "(" { Sort ","}* "}" ":" Sort Attributes
HookedSymbolDefinition ::=
    "hooked-symbol" SymbolId SortParameters "(" { Sort ","}* "}" ":" Sort Attributes

AliasDefinition ::=
    "alias" SymbolId SortParameters "(" { Sort ","}* "}" ":" Sort
        "where" ApplicationPattern ":=" Pattern
        Attributes

Axiom ::= "axiom" SortParameters Pattern Attributes
Claim ::= "claim" SortParameters Pattern Attributes

SortParameters ::= "{" {SortVariable ","}* "}"

SortVariable ::= SortId

Sort
  ::= SortVariable
    | SortId "{" { Sort ","}* "}"

Pattern
  ::= Variable
    | MLPattern
    | ApplicationPattern

Variable ::= ElemVar | SetVar

ElemVar ::= ElemVarId ":" Sort
SetVar ::= SetVarId ":" Sort

ApplicationPattern ::=
    SymbolId "{" { Sort ","}* "}" "(" { Pattern ","}* ")"

MLPattern
  ::=
    // Predicate Logic Connectives
      "\top" "{" Sort "}" "(" ")"
    | "\bottom" "{" Sort "}" "(" ")"
    | "\not" "{" Sort "}" "(" Pattern ")"
    | "\and" "{" Sort "}" "(" Pattern "," Pattern ")"
    | "\or" "{" Sort "}" "(" Pattern "," Pattern ")"
    | "\implies" "{" Sort "}" "(" Pattern "," Pattern ")"
    | "\iff" "{" Sort "}" "(" Pattern "," Pattern ")"
    // FOL quantifiers
    | "\exists" "{" Sort "}" "(" ElemVar "," Pattern ")"
    | "\forall" "{" Sort "}" "(" ElemVar "," Pattern ")"
    // Fixpoint operators
    | "\mu" "{" Sort "}" "(" SetVar "," Pattern ")"
    | "\nu" "{" Sort "}" "(" SetVar "," Pattern ")"
    // Definedness and totality
    | "\ceil" "{" Sort "," Sort "}" "(" Pattern ")"
    | "\floor" "{" Sort "," Sort "}" "(" Pattern ")"
    // Equality and membership
    | "\equals" "{" Sort "," Sort "}" "(" Pattern "," Pattern ")"
    | "\in" "{" Sort "," Sort "}" "(" Pattern "," Pattern ")"
    // Transition systems
    | "\next" "{" Sort "}" "(" Pattern ")"
    | "\rewrites" "{" Sort "}" "(" Pattern "," Pattern ")"
    // Domain values
    | "\dv" "{" Sort "}" "(" StringLiteral ")"
```
