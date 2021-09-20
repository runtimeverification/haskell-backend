# Kore Manual

## Table of Contents
1. [Introduction]()
  1. [Motivation]()
  1. [Document Structure]()
2. [Basics]()
3. [Design]()
3. [Implementation]()
4. [Language]()
5. [Commands]()
6. [K Framework]()
7. [Application Notes]()
8. [Glossary]()

## Introduction
### Motivation
### Document Structure
## Basics
## Design
## Implementation
## Language
## Commands
## K Framework
## Application Notes
## Glossary
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
