Attributes as Patterns
======================

Background
----------

Attributes are used in Kore in order to provide hints for manipulating symbols,
axioms, sorts and so on.
When translating from K, the Kore attributes are a
fairly direct translation of the K ones.

Each Kore backend can have its own set of attributes, and backends must be able
to ignore unknown attributes.

Examples include the `constructor` attribute which
specifies that a certain symbol has is a constructor, so, say, it
cannot be unified with different constructors.

Questions asked
---------------

1. What kind of structure do attributes have?
1. What syntax should we use?
1. How can we make sure that attributes have some documentation?

The answer to the first two questions comes from a Slack discussion on
`runtimeverification/#haskell` on 2018-17-25. The answer to the third
comes from a face-to-face discussion between traiansf and virgil-serbanuta.

Attribute structure
-------------------

Attributes are a name-value pair, where the value may be missing.

When present, the value is usually very simple, e.g. the `strict` attribute
can have a list of argument indexes in which it is strict.

Sometimes we may
want to refer to user-defined symbols, e.g. we may use the `unit` attribute
to specify the neutral element for an operation, and we may want to use this
attribute both for the operation symbol declaration and for the axioms that
make it a neutral element.

Similarly, we may want to use an `operation`
attribute with an operation symbol as argument to, say,
link an associativity axiom with an operation.

However, we can't tell what's the general structure of an attribute

Attribute syntax
----------------

We could encode each attribute as a string (name/key) or as a pair of
strings (key-value).
However, that does not seem a natural way of encoding
the structure that they have, and each backend would need its own
string-parsing library.

*Decision*: We will encode each attribute as a Kore term that uses only
application and `#String` patterns, with the top symbol giving the name
of the attribute.
Numbers will be encoded as strings. Therefore the following may be valid
attributes:
```
constructor{}()
strict{}("1", "2")
unit{}(epsilon{}())
operation{}(plus{}())
```
We will *not* check that this attributes are well-formed in the usual sense,
e.g. we will not check whether the `plus` operation in the example above has
two arguments or that the `strict` symbol arguments are object patterns or have
the `#Pattern` sort.
We *will* check that the top-level element is an application pattern since we
must be able to find its name.
We *may* check that the pattern uses only application and `#String` patterns.
We *will* require a backend to provide a validation function for each attribute
it can understand.

Encouraging documentation
-------------------------

While we cannot make sure that people document their attributes, we will do
the following:

When indexing a definition (or maybe when parsing), a backend must
provide a collection of default attributes for each entity that can have
attributes (e.g. module, symbol, axiom).

A backend must also provide a map from attribute names to a structure which
contains:
* A function which adds the attribute to an existing collection of attributes.
* A plain text description of the attribute.
* A plain text description of the attribute syntax.
* A validation function. We may provide a way of representing a
hierarchical structure wit documentation for each field, in which case the
plain-text syntax and part of the attribute documentation may be generated
automatically.

On the command line, we may add a flag which makes the verifier print all known
attributes with their documentation and syntax.

Attributes not present in this map will be wrapped in an opaque wrapper that,
in principle, can only be unwrapped by the unparsing code.
This parser will also be given to the function that adds attributes, in case
the backend wants to unparse them at some later point.

Attributes that do not pass validation will be provided in a list of
separate opaque wrappers, together with the error message provided by the
validator.

The indexed version of a Kore definition will only contain the backend's view of
the attributes.