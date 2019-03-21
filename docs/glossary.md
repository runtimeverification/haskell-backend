<a name="BMC"></a>*BMC*

1. (noun, acronym)
   Bounded model checking. Execute the program on all paths for a given number of steps (a.k.a. bound), attempting to identify given properties (bugs, unexpected behaviours, and so on) in the execution graph.

<a name="function"></a>*function*

1. (noun)
   An application symbol that, when applied to [function-like](#functionlike)
   patterns, produces function-like patterns.
1. (noun/adjective)
   A [function-like](#functionlike) pattern.

<a name="functionlike"></a>*function-like*

1. (adjective)
   A function-like pattern can have at most one value, i.e. it satisfies
   `(∃x . x=φ) ∨ ¬⌈φ⌉`.

<a name="functional"></a>*functional*

1. (adjective)
   A functional pattern has exactly one value, i.e. it satisfies `(∃x . x=φ)`.

<a name="pattern"></a>*pattern*

1. (noun)
   A syntactic element constructed according to the rules described in the
   semantics-of-k document.
2. (noun)
   The internal representation of such a syntactic element. It may have
   constructs which cannot be represented directly into syntactic elements
   (e.g. map domain values), but it is expected that it is possible to create
   an equivalent syntactic representation.

<a name="predicate"></a>*predicate*

1. (noun)
   A [pattern](#pattern) that can be evaluate only to top and bottom.
   Application patterns that can only evaluate to top and bottom are hard to
   identify, so some of the code that identifies predicates fails on these.
   Whenever a [substitution](#substitution) can be extracted efficiently,
   the "predicate" term may refer to the non-substitution part of the predicate.

<a name="SBC"></a>*SBC*

1. (noun, acronym)
   Semantics-based compilation. Compilation that uses the semantics of the
   language to analyze the behaviour of the program (e.g. through symbolic
   execution), and uses what it learned to improve the compilation result.

<a name="substitution"></a>*substitution*

1. (noun)
   A [predicate](#predicate) of the form `x1=φ1 ∧ x2=φ2 ∧ ... ∧ xn=φn` where
   `xi` are variables and `φi` are patterns.

<a name="termpattern"></a>*term pattern*

1. (noun)
   A [pattern](#pattern) of a specific type. A term pattern is usually
   constructed with variables and function application patterns, but,
   in many cases, it is used for any pattern with the expectation that it
   will be reduced, as much as reasonably possible,
   to a variable-application from.
