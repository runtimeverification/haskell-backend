# Kore Manual

## Table of Contents

1. [Introduction](#introduction)
    1. [Motivation](#introduction-motivation)
    2. [Document Structure](#introduction-document-structure)
2. [Basics](#basics)
3. [Design](#design)
3. [Implementation](#implementation)
    1. [Hooks](#implementation-hooks)
        1. [BOOL](#implementation-hooks-bool)
            1. [BOOL.Bool](#implementation-hooks-bool-bool)
            2. [BOOL.or](#implementation-hooks-bool-or)
            3. [BOOL.and](#implementation-hooks-bool-and)
            4. [BOOL.xor](#implementation-hooks-bool-xor)
            5. [BOOL.eq](#implementation-hooks-bool-eq)
            6. [BOOL.ne](#implementation-hooks-bool-ne)
            7. [BOOL.not](#implementation-hooks-bool-not)
            8. [BOOL.implies](#implementation-hooks-bool-implies)
        2. [INT](#implementation-hooks-int)
            1. [INT.Int](#implementation-hooks-int-int)
            2. [INT.gt](#implementation-hooks-int-gt)
            3. [INT.ge](#implementation-hooks-int-ge)
            4. [INT.eq](#implementation-hooks-int-eq)
            5. [INT.le](#implementation-hooks-int-le)
            6. [INT.lt](#implementation-hooks-int-lt)
            7. [INT.ne](#implementation-hooks-int-ne)
            8. [INT.add](#implementation-hooks-int-add)
            9. [INT.sub](#implementation-hooks-int-sub)
            10. [INT.mul](#implementation-hooks-int-mul)
            11. [INT.abs](#implementation-hooks-int-abs)
            12. [INT.tdiv](#implementation-hooks-int-tdiv)
            13. [INT.tmod](#implementation-hooks-int-tmod)
            14. [INT.ediv](#implementation-hooks-int-ediv)
            15. [INT.emod](#implementation-hooks-int-emod)
            16. [INT.and](#implementation-hooks-int-and)
            17. [INT.or](#implementation-hooks-int-or)
            18. [INT.xor](#implementation-hooks-int-xor)
            19. [INT.not](#implementation-hooks-int-not)
            20. [INT.shl](#implementation-hooks-int-shl)
            21. [INT.shr](#implementation-hooks-int-shr)
            22. [INT.pow](#implementation-hooks-int-pow)
            23. [INT.powmod](#implementation-hooks-int-powmod)
            24. [INT.log2](#implementation-hooks-int-log2)
        3. [STRING](#implementation-hooks-string)
            1. [STRING.String](#implementation-hooks-string-string)
            2. [STRING.eq](#implementation-hooks-string-eq)
            3. [STRING.lt](#implementation-hooks-string-lt)
            4. [STRING.concat](#implementation-hooks-string-concat)
            5. [STRING.string2int](#implementation-hooks-string-string2int)
            6. [STRING.int2string](#implementation-hooks-string-int2string)
            7. [STRING.string2base](#implementation-hooks-string-string2base)
            8. [STRING.base2string](#implementation-hooks-string-base2string)
            9. [STRING.substr](#implementation-hooks-string-substr)
            10. [STRING.length](#implementation-hooks-string-length)
            11. [STRING.find](#implementation-hooks-string-find)
            12. [STRING.token2string](#implementation-hooks-string-token2string)
            13. [STRING.string2token](#implementation-hooks-string-string2token)
        4. [MAP](#implementation-hooks-map)
            1. [MAP.Map](#implementation-hooks-map-map)
            2. [MAP.unit](#implementation-hooks-map-unit)
            3. [MAP.element](#implementation-hooks-map-element)
            4. [MAP.concat](#implementation-hooks-map-concat)
            5. [MAP.update](#implementation-hooks-map-update)
            6. [MAP.remove](#implementation-hooks-map-remove)
            7. [MAP.removeAll](#implementation-hooks-map-removeall)
            8. [MAP.size](#implementation-hooks-map-size)
            9. [MAP.lookup](#implementation-hooks-map-lookup)
            10. [MAP.lookupOrDefault](#implementation-hooks-map-lookupordefault)
            11. [MAP.in_keys](#implementation-hooks-map-inkeys)
            12. [MAP.keys](#implementation-hooks-map-keys)
            13. [MAP.keys_list](#implementation-hooks-map-keyslist)
            14. [MAP.values](#implementation-hooks-map-values)
            15. [MAP.inclusion](#implementation-hooks-map-inclusion)
        5. [LIST](#implementation-hooks-list)
            1. [LIST.List](#implementation-hooks-list-list)
            2. [LIST.unit](#implementation-hooks-list-unit)
            3. [LIST.element](#implementation-hooks-list-element)
            4. [LIST.concat](#implementation-hooks-list-concat)
            5. [LIST.get](#implementation-hooks-list-get)
            6. [LIST.update](#implementation-hooks-list-update)
            7. [LIST.in](#implementation-hooks-list-in)
            8. [LIST.size](#implementation-hooks-list-size)
            9. [LIST.make](#implementation-hooks-list-make)
            10. [LIST.updateAll](#implementation-hooks-list-updateall)
        6. [SET](#implementation-hooks-set)
            1. [SET.Set](#implementation-hooks-set-set)
            2. [SET.unit](#implementation-hooks-set-unit)
            3. [SET.element](#implementation-hooks-set-element)
            4. [SET.concat](#implementation-hooks-set-concat)
            5. [SET.intersection](#implementation-hooks-set-intersection)
            6. [SET.in](#implementation-hooks-set-in)
            7. [SET.inclusion](#implementation-hooks-set-inclusion)
            8. [SET.list2set](#implementation-hooks-set-list2set)
        7. [KEQUAL](#implementation-hooks-kequal)
            1. [KEQUAL.eq](#implementation-hooks-kequal-eq)
            2. [KEQUAL.neq](#implementation-hooks-kequal-neq)
            3. [KEQUAL.ite](#implementation-hooks-kequal-ite)
        8. [KRYPTO](#implementation-hooks-krypto)
            1. [KRYPTO.keccak256](#implementation-hooks-krypto-keccak266)
            2. [KRYPTO.ripemd160](#implementation-hooks-krypto-ripemd160)
            3. [KRYPTO.sha256](#implementation-hooks-krypto-sha256)
            4. [KRYPTO.sha3256](#implementation-hooks-krypto-sha3256)
        9. [BYTES](#implementation-hooks-bytes)
            1. [BYTES.bytes2string](#implementation-hooks-bytes-bytes2string)
            2. [BYTES.string2bytes](#implementation-hooks-bytes-string2bytes)
            3. [BYTES.update](#implementation-hooks-bytes-update)
            4. [BYTES.substr](#implementation-hooks-bytes-substr)
            5. [BYTES.replaceAt](#implementation-hooks-bytes-replaceat)
            6. [BYTES.padRight](#implementation-hooks-bytes-padright)
            7. [BYTES.padLeft](#implementation-hooks-bytes-padleft)
            8. [BYTES.reverse](#implementation-hooks-bytes-reverse)
            9. [BYTES.length](#implementation-hooks-bytes-length)
            10. [BYTES.concat](#implementation-hooks-bytes-concat)
            11. [BYTES.int2bytes](#implementation-hooks-bytes-int2bytes)
            12. [BYTES.bytes2int](#implementation-hooks-bytes-bytes2int)
            13. [BYTES.decodeBytes](#implementation-hooks-bytes-decodebytes)
            14. [BYTES.encodeBytes](#implementation-hooks-bytes-encodebytes)
    2. [Source Tree and Build System](#implementation-source-tree-and-build-system)
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
    1. [kore-exec](#commands-kore-exec)
    2. [kore-repl](#commands-kore-repl)
6. [K Framework](#kframework)
7. [Application Notes](#application-notes)
8. [Glossary](#glossary)

## [Introduction]{#introduction}

### [Motivation]{#introduction-motivation}

### [Document Structure]{#introduction-document-structure}

## [Basics]{#basics}

## [Design]{#design}

## [Implementation]{#implementation}

### [Hooks]{#implementation-hooks}

[Pull request #632](https://github.com/kframework/kore/pull/632/files) is a self-contained example of adding a builtin symbol. When adding a builtin symbol we should add:

1. An entry to the hooks document.
2. A symbol verifier.
3. An evaluator for concrete arguments (at least).
4. A declaration to `Test.Kore.Builtin.Definition`.
5. A few tests with different concrete arguments.

The builtin domains are listed below, categorized by sort. Each sort and symbol is described and an example hooked declaration is given. Note that some domains depend on others being defined!


#### [BOOL]{#implementation-hooks-bool}

No dependencies.

##### [BOOL.Bool]{#implementation-hooks-bool-bool}

The builtin Boolean sort:

```
hooked-sort Bool{}
    [hook{}("BOOL.Bool")]
```

Two domain values are recognized:

```
\dv{Bool{}}("true")  // Boolean true
\dv{Bool{}}("false") // Boolean false
```

##### [BOOL.or]{#implementation-hooks-bool-or}

Logical OR: `\dv{Bool{}}("true")` if either operand is `\dv{Bool{}}("true")`, otherwise `\dv{Bool{}}("false")`.

```
hooked-symbol or{}(Bool{}, Bool{}) : Bool{}
    [hook{}("BOOL.or")]
```


##### [BOOL.and]{#implementation-hooks-bool-and}

Logical AND: `\dv{Bool{}}("true")` if both operands are `\dv{Bool{}}("true")`, otherwise `\dv{Bool{}}("false")`.

```
hooked-symbol and{}(Bool{}, Bool{}) : Bool{}
    [hook{}("BOOL.and")]
```

##### [BOOL.xor]{#implementation-hooks-bool-xor}

Logical XOR: `\dv{Bool{}}("true")` if exactly one operand is `\dv{Bool{}}("true")`, otherwise `\dv{Bool{}}("false")`.

```
hooked-symbol xor{}(Bool{}, Bool{}) : Bool{}
    [hook{}("BOOL.xor")]
```

##### [BOOL.eq]{#implementation-hooks-bool-eq}

`\dv{Bool{}}("true")` if the operands are equal, otherwise `\dv{Bool{}}("false")`.

```
hooked-symbol eq{}(Bool{}, Bool{}) : Bool{}
    [hook{}("BOOL.eq")]
```

##### [BOOL.ne]{#implementation-hooks-bool-ne}

`\dv{Bool{}}("true")` if the operands are **not** equal, otherwise `\dv{Bool{}}("false")`.

```
hooked-symbol ne{}(Bool{}, Bool{}) : Bool{}
    [hook{}("BOOL.ne")]
```

##### [BOOL.not]{#implementation-hooks-bool-not}

Logical negation: `\dv{Bool{}}("true")` when its argument is `\dv{Bool{}}("false")` and vice versa.

```
hooked-symbol not{}(Bool{}, Bool{}) : Bool{}
    [hook{}("BOOL.not")]
```

##### [BOOL.implies]{#implementation-hooks-bool-implies}

Logical implication.

```
hooked-symbol implies{}(Bool{}, Bool{}) : Bool{}
    [hook{}("BOOL.implies")]
```

#### [INT]{#implementation-hooks-int}

Depends on `BOOL`.

##### [INT.Int]{#implementation-hooks-int-int}

The builtin sort of arbitrary-precision integers.

```
hooked-sort Int{}
    [hook{}("INT.Int")]
```

Valid domain values are a string of decimal digits, optionally preceeded by a sign.

```
\dv{Int{}}("256")   // positive 256, sign omitted
\dv{Int{}}("-1024") // negative 1024
\dv{Int{}}("+3")    // positive 3
```

##### [INT.gt]{#implementation-hooks-int-gt}

Comparison: is the first argument greater than the second?

```
hooked-symbol gt{}(Int{}, Int{}) : Bool{}
    [hook{}("INT.gt")]
```

##### [INT.ge]{#implementation-hooks-int-ge}

Comparison: is the first argument greater than or equal to the second?

```
hooked-symbol ge{}(Int{}, Int{}) : Bool{}
    [hook{}("INT.ge")]
```

##### [INT.eq]{#implementation-hooks-int-eq}

Comparison: is the first argument equal to the second?

```
hooked-symbol eq{}(Int{}, Int{}) : Bool{}
    [hook{}("INT.eq")]
```

##### [INT.le]{#implementation-hooks-int-le}

Comparison: is the first argument less than or equal to the second?

```
hooked-symbol le{}(Int{}, Int{}) : Bool{}
    [hook{}("INT.le")]
```

##### [INT.lt]{#implementation-hooks-int-lt}

Comparison: is the first argument less than the second?

```
hooked-symbol lt{}(Int{}, Int{}) : Bool{}
    [hook{}("INT.lt")]
```

##### [INT.ne]{#implementation-hooks-int-ne}

Comparison: is the first argument inequal to the second?

```
hooked-symbol ne{}(Int{}, Int{}) : Bool{}
    [hook{}("INT.ne")]
```

##### [INT.add]{#implementation-hooks-int-add}

The sum of the arguments.

```
hooked-symbol add{}(Int{}, Int{}) : Int{}
    [hook{}("INT.add")]
```

##### [INT.sub]{#implementation-hooks-int-sub}

The difference of the arguments (the first less the second).

```
hooked-symbol sub{}(Int{}, Int{}) : Int{}
    [hook{}("INT.sub")]
```

##### [INT.mul]{#implementation-hooks-int-mul}

The product of the arguments.

```
hooked-symbol mul{}(Int{}, Int{}) : Int{}
    [hook{}("INT.mul")]
```

##### [INT.abs]{#implementation-hooks-int-abs}

The absolute value of the argument.

```
hooked-symbol abs{}(Int{}) : Int{}
    [hook{}("INT.abs")]
```

##### [INT.tdiv]{#implementation-hooks-int-tdiv}

Quotient of the first argument divided by the second (truncated toward zero). The result is `bottom{}()` if the second argument is zero.

```
hooked-symbol tdiv{}(Int{}, Int{}) : Int{}
    [hook{}("INT.tdiv")]
```

##### [INT.tmod]{#implementation-hooks-int-tmod}

Remainder of the first argument divided by the second (truncated toward zero). The result is `bottom{}()` if the second argument is zero.

```
hooked-symbol tmod{}(Int{}, Int{}) : Int{}
    [hook{}("INT.tmod")]
```

##### [INT.ediv]{#implementation-hooks-int-ediv}

Quotient of the first argument divided by the second (using the euclidean algorithm). The result is `bottom{}()` if the second argument is zero.

```
hooked-symbol ediv{}(Int{}, Int{}) : Int{}
    [hook{}("INT.ediv")]
```

##### [INT.emod]{#implementation-hooks-int-emod}

Remainder of the first argument divided by the second (using the euclidean algorithm). The result is guaranteed to be positive. The result is `bottom{}()` if the second argument is zero.

```
hooked-symbol emod{}(Int{}, Int{}) : Int{}
    [hook{}("INT.emod")]
```

##### [INT.and]{#implementation-hooks-int-and}

Bitwise and of the arguments.

```
hooked-symbol and{}(Int{}, Int{}) : Int{}
    [hook{}("INT.and")]
```

##### [INT.or]{#implementation-hooks-int-or}

Bitwise or of the arguments.

```
hooked-symbol or{}(Int{}, Int{}) : Int{}
    [hook{}("INT.or")]
```

##### [INT.xor]{#implementation-hooks-int-xor}

Bitwise exclusive or of the arguments.

```
hooked-symbol xor{}(Int{}, Int{}) : Int{}
    [hook{}("INT.xor")]
```

##### [INT.not]{#implementation-hooks-int-not}

Bitwise complement of the argument.

```
hooked-symbol not{}(Int{}) : Int{}
    [hook{}("INT.not")]
```

##### [INT.shl]{#implementation-hooks-int-shl}

Shift the bits of the first argument to the left. The second argument specifies how many bits to shift by, and will be truncated to the least-significant Haskell Int. The second argument can be negative, in which case the first argument will be shifted right.

```
hooked-symbol shl{}(Int{}, Int{}) : Int{}
    [hook{}("INT.shl")]
```

##### [INT.shr]{#implementation-hooks-int-shr}

Shift the bits of the first argument to the right. The second argument specifies how many bits to shift by, and will be truncated to the least-significant Haskell Int. The second argument can be negative, in which case the first argument will be shifted left.

```
hooked-symbol shr{}(Int{}, Int{}) : Int{}
    [hook{}("INT.shr")]
```

##### [INT.pow]{#implementation-hooks-int-pow}

The first argument raised to the power of the second argument. The result is `bottom{}()` if the second argument is negative.

```
hooked-symbol pow{}(Int{}, Int{}) : Int{}
    [hook{}("INT.pow")]
```

##### [INT.powmod]{#implementation-hooks-int-powmod}

The first argument raised to the power of the second argument, but performed modulo the third argument. The result is `\bottom{}()` if either:

* The second argument is zero, or
* the second argument is negative and the first and third arguments are not coprime.

```
hooked-symbol powmod{}(Int{}, Int{}, Int{}) : Int{}
    [hook{}("INT.powmod")]
```

##### [INT.log2]{#implementation-hooks-int-log2}

The base 2 logarithm of the argument. The result is `\bottom{}()` if the second argument is not positive.

```
hooked-symbol log2{}(Int{}) : Int{}
    [hook{}("INT.log2")]
```

## [Language]{#language}

### [Lexical Structure]{#language-lexical-structure}

#### [Comments]{#language-lexical-structure-comments}

Kore allows C-style comments:

* `//` line comment
* `/*` block comment (non-nested) `*/`

#### [String literals]{#language-lexical-structure-string-literals}

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

#### [Keywords]{#language-lexical-structure-keywords}

```
<keyword>
  ::= "module"  | "endmodule"
    | "import"
    | "sort"    | "hooked-sort"
    | "symbol"  | "hooked-symbol"
    | "axiom"   | "claim"
    | "alias"   | "where"
```

#### [Identifiers]{#language-lexical-structure-identifiers}

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

### [Syntax]{#language-syntax}

The syntax of Kore is defined here in [Backus-Naur form](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form), augmented with the following meta-syntactic notations for brevity:

```
<[$item]-sep-by-[$separator]>
  ::= ""
    | <[$item]-sep-by-1-[$separator]>

<[$item]-sep-by-1-[$separator]>
  ::= $item
    | $item $separator <[$item]-sep-by-1-[$separator]>

```

#### [Sorts]{#language-syntax-sorts}

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

#### [Patterns]{#language-syntax-patterns}

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

#### [Attributes]{#language-syntax-attributes}

Attributes are hints to the backend, often collected by the frontend. Some attributes express syntactic information, while others express semantic information. All semantic information contained in attributes should correspond to axioms declared explicitly. The hints indicate when the backend may use faster algorithms, more efficient data structures, etc. (TODO be more specific). The meaning of particular attributes is implementation-defined. The order of attributes is **never** significant.

```
<attribute>
  ::= <application-pattern>

<attributes>
  ::= <[attribute]-sep-by-[","]>
```

#### [Sentences]{#language-syntax-sentences}

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

#### [Definition and modules]{#language-syntax-definition-and-modules}

A definition is a non-empty sequence of modules.

```
<definition>
  ::= "[" <attributes> "]" <modules>

<module>
  ::= "module" <module-name> <sentences> "endmodule" "[" <attributes> "]"

<modules>
  :: <[module]-sep-by-1-[whitespace]>
```

### [Validity]{#language-validity}

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

### [Implicit Sort Signatures]{#language-implicit-sort-signatures}

#### [Connectives]{#language-implicit-sort-signatures-connectives}

```
\top{S}() : S
\bottom{S}() : S
\not{S}(S) : S
\and{S}(S, S) : S
\or{S}(S, S) : S
\implies{S}(S, S) : S
\iff{S}(S, S) : S
```

#### [Quantifiers]{#language-implicit-sort-signatures-quantifiers}

```
\exists{S}(x:T, S)
\forall{S}(x:T, S)
```

#### [Fixpoints]{#language-implicit-sort-signatures-fixpoints}

```
\mu{}(@X:S, S) : S
\nu{}(@X:S, S) : S
```

#### [Rewriting]{#language-implicit-sort-signatures-rewriting}

```
\next{S}(S) : S
\rewrites{S}(S, S) : S
```

#### [Domain values]{#language-implicit-sort-signatures-domain-values}

```
\dv{S}(#String) : S
```

## [Commands]{#commands}

### [kore-exec]{#commands-kore-exec}

### [kore-repl]{#commands-kore-repl}

## [K Framework]{#kframework}

## [Application Notes]{#application-notes}

## [Glossary]{#glossary}

[*BMC*]{#glossary-bmc}

  1. (noun, acronym) Bounded model checking. Execute the program on all paths for a given number of steps (a.k.a. bound), attempting to identify given properties (bugs, unexpected behaviours, etc.) in the execution graph.

[*constructor-like*]{#glossary-constructor-like}

  1. (adjective) A pattern is *constructor-like* if logical equality is syntactic equality. A [pattern](#glossary-pattern) is constructor-like if it is logically equal (in the `\equals` sense) to another constructor-like pattern if and only if the patterns are syntactically equal. The constructor-like patterns of a sort comprise a normal form of elements in that sort.
  2. (adjective) A symbol is *constructor-like* if it may form the head of a constructor-like application pattern (in the sense defined about). Roughly, this means the symbol has injectivity and no-confusion axioms.

[*function*]{#glossary-function}

  1. (noun) An application symbol that, when applied to [function-like](#glossary-function-like) patterns, produces function-like patterns.
  2. (noun/adjective) A [function-like](#glossary-function-like) pattern.

[*function-like*]{#glossary-function-like}

  1. (adjective) A function-like [pattern](#glossary-pattern) can have at most one value, i.e. it satisfies $(\exists x . x = \varphi ) \vee \neg \lceil \varphi \rceil$.

[*functional*]{#glossary-functional}

  1. (adjective) A functional [pattern](#glossary-pattern) has exactly one value, i.e. it satisfies $(\exists x . x = \varphi)$.

[*pattern*]{#glossary-pattern}

  1. (noun) The internal representation of a syntactic element. It may have constructs which cannot be represented directly into syntactic elements (e.g. map domain values), but it is expected that it is possible to create an equivalent syntactic representation.

[*predicate*]{#glossary-predicate}

  1. (noun) A [pattern](#glossary-pattern) that can evaluate only to top and bottom. Application patterns that can only evaluate to top and bottom are hard to identify (TODO Why?), so some of the code that identifies predicates fails on these (TODO clarify what code?). Whenever a [substitution](#glossary-substitution) can be extracted efficiently, the "predicate" term may refer to the non-substitution part of the predicate.

[*SBC*]{#glossary-sbc}

  1. (noun, acronym) Semantics-based compilation. Compilation that uses the semantics of the language to analyze the behaviour of the program (e.g. through symbolic execution), and uses what it learned to improve the compilation result.

[*sort injection*]{#glossary-sort-injection}

  1. (noun) A [symbol](#glossary-symbol) with the `sortInjection` attribute. The sort injection symbol is used to represent the K sub-sort relation in Kore. K sorts contain symbols and sorts (their sub-sorts), but Kore sorts contain only symbols. The sort injection symbol wraps patterns of a sub-sort so they can be included (*injected*) into the super-sort. Two important properties follow from this definition. First, sort injection symbols are injective. Second, the sort injection symbol from a particular sub-sort is distinct (in the no-confusion-different-constructors sense) from the super-sort's constructors.
  2. (noun) A sort injection is a [pattern](#glossary-pattern) of the form $inj\{Sub\{\}, Super\{\}\}(\varphi:Sub\{\})$ where `inj{Sub{}, Super{}}` is a sort injection symbol (described above). Where the K sort `Super` contains `Sub`, the pattern $\varphi$ with least-sort `Sub` can appear anywhere that a term of sort `Super` is required. In Kore, this is represented with the injection above because all sorts are regarded as distinct.

[*substitution*]{#glossary-substitution}

  1. (noun) A [predicate](#glossary-predicate) of the form $x_1=\varphi_1 \land x_2=\varphi_2 \land \dots \land x_n=\varphi_n$ where $x_i$ are variables and $\varphi_i$ are patterns.

[*symbol]{#glossary-symbol}

  1. TODO

[*term pattern*]{#glossary-term-pattern}

  1. (noun) A [pattern](#glossary-pattern) of a specific type. A term pattern is usually constructed with variables and function application patterns. In some cases, it is used for any pattern with the expectation that it will be reduced, as much as reasonably possible, to a variable-application form.
