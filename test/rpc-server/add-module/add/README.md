# Add module with `add-module` endpoint

This test uses [a-to-f](../../resources/a-to-f/) [definition](../../resources/a-to-f/definition.kore) split into two parts: first, the part without the `TEST` module is loaded when `kore-rpc` starts, and then the `TEST` module is added using the `add-module` endpoint [parameters](./params.json).

Expected:
* Module successfully added.
