JSON RPC Server API
===================

This document details the API and working of the `kore-rpc` executable. This binary has a similar CLI interface to `kore-exec` and running

```bash
kore-rpc <DEFINITION>.kore --module <MODULE> --server-port <PORT>
```

will parse the `<DEFINITION>.kore` file with `<MODULE>` as the main module and then launch a JSON RPC server on port `<PORT>`.

The server runs over sockets and can be interacted with by sending JSON RPC messages. Note that the server listens over raw sockets and doesn't use a high(er)-level protocol like HTTP.

# API

## Execute

### Request:

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "execute",
  "params": {
    "max-depth": 1,
    "cut-point-rules": ["rule1"],
    "terminal-rules": ["ruleFoo"],
    "state": {
      "format": "KORE",
      "version": 1,
      "term": {}
    }
  }
}
```

Optional parameters: `max-depth`, `cut-point-rules`, `terminal-rules`

_Note: `id` can be an int or a string and each message must have a new `id`. The response objects have the same id as the message._


### Error Response:

If the message is malformed, e.g. the state is not serialized properly, the server will return

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "data": {
      "max-depth": 1,
      "cut-point-rules": ["rule1"],
      "terminal-rules": ["ruleFoo"],
      "state": {
        "format": "KORE",
        "version": 1,
        "term": {}
      }
    },
    "code": -32602,
    "message": "Invalid params"
  }
}
```

If the verification of the `state` pattern fails, the following error is returned:

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "data": {
      "context": [
          "symbol or alias \'Lbl\'-LT-\'generatedTop\'-GT-\'\' (<unknown location>)","symbol or alias \'Lbl\'-LT-\'k\'-GT-\'\' (<unknown location>)","symbol or alias \'kseq\' (<unknown location>)","symbol or alias \'inj\' (<unknown location>)","symbol or alias \'Lbl\'UndsUndsUnds\'TESTFOO-SYNTAX\'Unds\'Stmt\'Unds\'Stmt\'Unds\'Stmt\' (<unknown location>)"
      ],
      "error": "Head \'Lbl\'UndsUndsUnds\'TESTFOO-SYNTAX\'Unds\'Stmt\'Unds\'Stmt\'Unds\'Stmt\' not defined."
    },
    "code": -32002,
    "message": "Could not verify KORE pattern"
  }
}
```


### Correct Response:

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "states": [
      {
        "state": {"format":"KORE", "version":1, "term":{}},
        "depth": 1
      }
    ],
    "reason": "final-state"
  }
}
```

The above will be also be the same for:
  * `"reason": "stuck"`
  * `"reason": "depth-bound"`
  * `"reason": "cut-point-rule"`
  * `"reason": "terminal-rule"`

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "states": [
      {
        "state": {"format": "KORE", "version": 1, "term": {}},
        "depth": 5,
        "condition": {
          "substitution": {"format": "KORE", "version": 1, "term": {}},
          "predicate": {"format": "KORE", "version": 1, "term": {}}
        }
      },
      {
        "state": {"format": "KORE", "version": 1, "term": {}},
        "depth": 5,
        "condition": {
          "substitution": {"format": "KORE", "version": 1, "term": {}},
          "predicate": {"format": "KORE", "version": 1, "term": {}}
        }
      }
    ],
    "reason": "branching"
  }
}
```

## Implies

### Request:

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "implies",
  "params": {
    "antecedent": {"format": "KORE", "version": 1, "term": {}},
    "consequent": {"format": "KORE", "version": 1, "term": {}}
  }
}
```

### Error Response:

Same as for execute

### Correct Response:

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "satisfiable": false
  }
}
```

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "satisfiable": true,
    "condition": {
      "substitution": {"format": "KORE", "version": 1, "term": {}},
      "predicate": {"format": "KORE", "version": 1, "term": {}}
    }
  }
}
```


## Simplify

### Request:

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "simplify",
  "params": {
    "state": {"format": "KORE", "version": 1, "term": {}}
  }
}
```

### Error Response:

Same as for execute

### Correct Response:

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "state": {"format": "KORE", "version": 1, "term": {}}
  }
}
```

## Cancel

### Request:

```json
{"jsonrpc": "2.0", "method": "cancel"}
```

### Response:

none

### Response from cancelled call:

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "code": -32000,
    "message": "Request cancelled"
  }
}
```
