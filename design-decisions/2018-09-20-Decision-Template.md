Decision Template
=================

Background
----------

We are writing decision documents for each decision that we want to record.
These live in the `design-decisions` directory, using file names with
the `yyyy-mm-dd-<dash-separated-title>.md` format, with the date
being roughly the date when the decision was made.

Currently the document format is unrestricted, but loosely
follows the template in this file.

Problem/Questions
-----------------

Should we follow a template when writing decision documents?

What should happen with the old document when re-deciding on an issue?

Decision: Strongly recommended template
---------------------------------------

We should consider the current template as a strong suggestion, without
being forced to follow it when it does not make sense.

Decision: Prefix with OBSOLETE
------------------------------

When replacing a decision with another one, we will prefix the replaced
decision title with `OBSOLETE`, both in the document and in the
file name. As an example, this file's name will become
`2018-09-20-OBSOLETE-Decision-Template.md`.

The obsolete document should have one line right after
the main title saying "Replaced by <file-name>." The new document
may have a similar line saying "Replacing <file-name>."

At some later point we may move the obsolete documents to a
separate directory.

Reasoning/Other options considered
----------------------------------

The proposed structure makes the documents easier to read: one can quickly
identify the issue and the decisions around it. People can easily
refresh their background knowledge. When someone asks "why?",
or someone wants to make a better decision, they can read the "reasoning"
section.

The template is strongly suggested because it is expected that most
decisions will have some background, some issue(s) that need to be decided,
some actual decisions and some reasoning behind them. However, the
"Reasoning" section may need to be structured differently, other sections
may be needed (e.g. an examples one) and, in general, if something else
makes sense, then it makes sense.

The other option considered was to not use a template and to point out
possible improvements in code reviews. Since people loosely followed this
template anyway, the current decision does not change the end result much,
and it makes the code reviews focus on the important stuff. It also
makes it less likely that people don't forget to include
important/useful things in decision documents.
