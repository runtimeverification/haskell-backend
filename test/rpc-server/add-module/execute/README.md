# Execute module added with `add-module` endpoint

This test uses [a-to-f](../../resources/a-to-f/) [definition](../../resources/a-to-f/definition.kore).

An `execute` request starting from state `c` is sent several times.

The request is sent twice with optional parameter `"module": "NEW"`
before and after adding the `NEW` module with the [`add-module`
test](./add).

Expected:
* [Fail](./response-fail.golden), error message when run before adding the `NEW` module.
* [Success](./response-success.golden), gets `stuck` in state `f` when run after adding the `NEW` module.

In addition, the request is sent without the `module` parameter before
and after adding the `NEW` module.

Expected:
* [Default](./response-defaultmodule.golden), gets `stuck` in state `d`.
