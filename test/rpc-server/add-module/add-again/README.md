# Add module with `add-module` endpoint again

This test uses [a-to-f](../../resources/a-to-f/) [definition](../../resources/a-to-f/definition.kore) split into two parts:

When the server starts, a `TEST` module is loaded which contains the following transitions:

```
      a
     / \
    V   V
    b   c
        |
        V
        d
```

Then a `NEW` module is added using the `add-module` endpoint [parameters](./params.json),
adding the following transitions:


```
        d
        |
        V
        e
        |
        V
        f
```

Expected:
* Module successfully added even though it has been added already, because the content is exactly the same.
