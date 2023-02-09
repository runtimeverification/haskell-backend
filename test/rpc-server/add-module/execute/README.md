# Execute module added with `add-module` endpoint

This test uses [a-to-f](../../resources/a-to-f/) [definition](../../resources/a-to-f/definition.kore). The test is run twice before and after adding the `TEST` module with the [`add-module` test](./add).

Expected:
* [Fail](./response-fail.golden) if run before adding the `TEST` module.
* [Success](./response-success.golden) if run after adding the `TEST` module.
