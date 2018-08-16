Repeated Attributes
===================

Background
==========

Kore attributes are all named by their top level.
The question is whether it should be allowed to have multiple
attributes with the same name in an attribute list.

In cases like of argument-less attributes like "function" or
"constructor" there is no gain to having multiple copies of
an attribute.

The question is, should this be forbidden in general.

Advantages
-----------

Some attributes should not be repeated.

Allowing no repeated attributes would allow using a
simple map to organize all attributes, even those
a backend does not specially understand

Counterarguments
----------------

Other attributes may make sense to repeat, such as
a formatting attribute describing how to pretty-print
a certain construct in different output formats.
(These cases could also be handled without repetition by
defining a way to represent lists of sub-items within
a single top-level attribute).

Backends may already impose specific well-formedness
checks on attributes they understand, which can include
banning repetition of specific known attributes.

Multi-map data structures are readily available,
and allow efficient access to attributes by name
whether or not we forbid repetitions.

Decision
========

We will not forbid repeated attributes in general.

* This restriction can be imposed per-attribute in backends
  without adding a global restriction to the design of Kore
* There appears to be no theoretical simplification of the
  Kore language considering attributes are already uninterpreted
* Multi-maps should allow efficient indexing of attributes
  even without forbidding repeated names.
