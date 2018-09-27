Hook Attribute
==============

Background
----------

In [Attributes as Patterns](./2018-07-25-Attributes-as-patterns.md), we decided
to encode attributes as Kore patterns consisting of symbols, application, and
string literals.

The `hook` attribute in particular is used to associated defined sorts and
symbols with builtin domains implemented in the backend. Sorts and symbols in
builtin domains may be declared with the `hooked-sort` and `hooked-symbol`
declarations, respectively.

Questions
---------

1. Is a `hooked-sort` or `hooked-symbol` declaration valid without a `hook`
   attribute?
2. Is the `hook` attribute valid outside a hooked declaration?

Decision: Hooked declarations are valid without the `hook` attribute
--------------------------------------------------------------------

The semantics of hooked sorts and symbols are entirely
implementation-defined. Any one semantic interpretation of a hooked sort or
symbol is as valid as any other interpretation, including no interpretation (no
hook) at all.

Decision: The `hook` attribute is invalid outside a hooked declaration
----------------------------------------------------------------------

The semantics of ordinary sorts and symbols are entirely defined in Kore;
therefore, the implementation must not honor any `hook` attribute on ordinary
sorts and symbols because that might violate the defined semantics.

When attribute verification is enabled, attaching a `hook` attribute to an
ordinary sort or symbol declaration should be an error; otherwise, such a `hook`
attribute should be silently ignored.

Other options considered
------------------------

Refer to [this discussion](https://runtimeverification.slack.com/archives/CC360GUTG/p1537887224000100).

We also considered removing `hooked-sort` and `hooked-symbol` and looking
instead for a `hook` attribute on ordinary sort and symbol declarations. This
proposal was rejected because it would make the `hook` attribute semantically
significant. (Attributes must not be semantically significant.)
