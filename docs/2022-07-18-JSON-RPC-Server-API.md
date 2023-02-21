JSON RPC Server API
===================

This document details the API and working of the `kore-rpc` executable. This binary has a similar CLI interface to `kore-exec` and running

```bash
kore-rpc <DEFINITION>.kore --module <MODULE> --server-port <PORT>
```

will parse the `<DEFINITION>.kore` file with `<MODULE>` as the main module and then launch a JSON RPC server on port `<PORT>`.

The server runs over sockets and can be interacted with by sending JSON RPC messages. Note that the server listens over raw sockets and doesn't use a high(er)-level protocol like HTTP. The server sends responses as single line strings, with `\n` used as the message delimiter. The server allows for bidirectional communication and once opened, a socket connection can be maintained throughout the session. However, this is not strictly necessary as all the API functions (except for `cancel`) are pure. Also note that the server uses the `id` of the request message as the `id` of the response, which allows the client to link responses back to their requests. It is therefore important to always send a unique `id` with each request witin the current socket session.

# API

## Execute

### Request:

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "execute",
  "params": {
    "max-depth": 4,
    "cut-point-rules": ["rule1"],
    "terminal-rules": ["ruleFoo"],
    "moving-average-step-timeout": true,
    "step-timeout": 1234,
    "module": "MODULE-NAME",
    "state": {
      "format": "KORE",
      "version": 1,
      "term": {}
    }
  }
}
```

Optional parameters: `max-depth`, `cut-point-rules`, `terminal-rules`, `moving-average-step-timeout`, `step-timeout` (timeout is in milliseconds), `module` (main module name)

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

All correct responses have a result containing a `reason`, with one of the following values:
* `"reason": "branching"`
* `"reason": "stuck"`
* `"reason": "depth-bound"`
* `"reason": "cut-point-rule"`
* `"reason": "terminal-rule"`
* `"reason": "timeout"`
* `"reason": "aborted"`

A field `state` contains the state reached (including optional `predicate` and `substitution`), a field `depth` indicates the execution depth.

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "state": {
      "term": {"format":"KORE", "version":1, "term":{}},
      "predicate": {"format":"KORE", "version":1, "term":{}},
      "substitution": {"format":"KORE", "version":1, "term":{}},
    },
    "depth": 1
    "reason": "stuck"
  }
}
```

The above will be also be the same for:
  * `"reason": "depth-bound"`
  * `"reason": "timeout"`
  * `"reason": "aborted"`

If `"reason":  "terminal-rule"`, an additional `rule` field indicates which of the `terminal-rule` labels or IDs led to terminating the execution:

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "state": {
      "term": {"format":"KORE", "version":1, "term":{}},
      "predicate": {"format":"KORE", "version":1, "term":{}},
      "substitution": {"format":"KORE", "version":1, "term":{}},
    },
    "depth": 1,
    "reason": "terminal-rule",
    "rule": "ruleFoo"
  }
}
```


If `"reason": "branching"`, an additional `next-states` field contains all following states of the branch point.
```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "state": {
      "term": {"format":"KORE", "version":1, "term":{}},
      "predicate": {"format":"KORE", "version":1, "term":{}},
      "substitution": {"format":"KORE", "version":1, "term":{}},
    },
    "depth": 2,
    "reason": "branching",
    "next-states": [
      {
        "term": {"format": "KORE", "version": 1, "term": {}},
        "predicate": {"format":"KORE", "version":1, "term":{}},
        "substitution": {"format":"KORE", "version":1, "term":{}},
      },
      {
        "term": {"format": "KORE", "version": 1, "term": {}},
        "predicate": {"format":"KORE", "version":1, "term":{}},
        "substitution": {"format":"KORE", "version":1, "term":{}},
      }
    ]
  }
}
```

If `"reason": "cut-point-rule"`, the `next-states` field contains the next state (if any) in a list. The `rule` field indicates which rule led to stopping.

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "state": {
      "term": {"format":"KORE", "version":1, "term":{}},
      "predicate": {"format":"KORE", "version":1, "term":{}},
      "substitution": {"format":"KORE", "version":1, "term":{}},
    },
    "depth": 2,
    "reason": "cut-point-rule",
    "rule": "rule1",
    "next-states": [
      {
        "term": {"format": "KORE", "version": 1, "term": {}},
        "predicate": {"format":"KORE", "version":1, "term":{}},
        "substitution": {"format":"KORE", "version":1, "term":{}},
      }
    ]
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
    "consequent": {"format": "KORE", "version": 1, "term": {}},
    "module": "MODULE-NAME"
  }
}
```

Optional parameters: `module` (main module name)

### Error Response:

Errors in decoding the `antecedent` or `consequent` terms are reported similar as for execute.

Other errors are specific to the implication checker and what it supports. These errors are reported as `Implication check error` (also see below):

* Currently, terms that do not simplify to a singleton pattern are not supported. Unsupported terms are typically those which have an `\or` at the top level.

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "data": {
      "context": [
        "LHS: \\and{SortK{}}(     /* term: */ /* D Spa */ \\or{SortK{}}( /* Fl Fn D Sfa */ Configa:SortK{}, /* Spa */ \\not{SortK{}}( /* Fl Fn D Sfa */ Configa:SortK{} ) ), \\and{SortK{}}(     /* predicate: */ /* D Sfa */ \\top{SortK{}}(),     /* substitution: */ \\top{SortK{}}() ))"
      ],
      "error": "Term does not simplify to a singleton pattern"
    }
    "code": -32003,
    "message": "Implication check error"
  }
}
```

* The `antecedent` term must not have free variables that are used as existentials in the `consequent`.
* The `consequent` term must not have free variables that are not also free in the `antecedent`.
* The `antecedent` term must be function-like.
* `antecedent` and `consequent` must have the same sort.

### Correct Response:

The endpoint simplifies `antecedent` and `consequent` terms and checks whether the implication holds. The simplified implication is returned (as a KORE term) in field `implication`.

If the implication holds, `satisfiable` is `true` and `condition` contains a unifying condition for the simplified antecedent and consequent (as provided in `implication`).

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "implication":  {"format": "KORE", "version": 1, "term": {}},
    "satisfiable": true,
    "condition": {
      "substitution": {"format": "KORE", "version": 1, "term": {}},
      "predicate": {"format": "KORE", "version": 1, "term": {}}
    }
  }
}
```

If the implication cannot be shown to hold, `satisfiable` is false.

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "implication":  {"format": "KORE", "version": 1, "term": {}},
    "satisfiable": false
  }
}
```

In some cases, a unifier `condition` for the implication can still be provided, although the implication cannot be shown to be true.

The endpoint implements the following specification:
- `antecedent` is `\\bottom` (implication holds trivially) => `satisfiable = True` and `condition = \\bottom`
- `consequent` is `\\bottom` and `antecedent` is not `\\bottom` => `satisfiable = False` and `condition = \\bottom`
- implication holds (not trivial) => `satisfiable = True` and `condition /= \\bottom`
- implication doesn't hold and the two terms do not unify,
indicating that the program configuration can be rewritten further => `satisfiable = False` and `condition` is omitted
- implication doesn't hold and the two terms unify, indicating that the configuration is stuck => `satisfiable = False` and `condition /= \\bottom`

## Simplify

### Request:

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "simplify",
  "params": {
    "state": {"format": "KORE", "version": 1, "term": {}},
    "module": "MODULE-NAME"
  }
}
```

Optional parameters: `module` (main module name)

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

## Add-module

### Request

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "add-module",
  "params": {
    "name": "MODULE-NAME",
    "module": "<plain text>"
  }
}
```

* `name` is the name of the main module.
* `module` is module represented in KORE.

### Correct Response:

Responds with an empty array if successful.

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": []
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


# API Error codes

The server uses the JSON RPC spec way of returning errors. Namely, the returned object will be of the form

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "code": -32002,
    "message": "Could not verify KORE pattern",
    "data": {}
  }
}
```

The kore-rpc specific error messages will use error codes in the range -32000 to -32099 and are listed for individual calles above as well as collected below for convenience.

## -32001 Cancel request unsupported in batch mode

Due to the way that cancel is implemented, we do not allow a cancel message within batch mode. This message should never occur if batch mode is not used.

## -32002 Could not verify KORE pattern

This error wraps the internal error thrown when validating the received pattern agains the loaded definition file.

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "code": -32002,
    "message": "Could not verify KORE pattern",
    "data": {
      "context": ["\\top (<unknown location>)","sort 'IntSort' (<unknown location>)","(<unknown location>)"],
      "error": "Sort 'IntSort' not defined."
    }
  }
}
```

## -32003 Implication check error

This error wraps an error message from the internal implication check routine, in case the input data is inconsistent or otherwise unsuitable for the check.

```json
{
  "jsonrpc":"2.0",
  "id":1
  "error": {
    "code": -32003,
    "message": "Implication check error",
    "data": {
      "context": [
        "/* Sfa */ \\mu{}( Config@A:SortK{}, /* Sfa */ Config@A:SortK{} )"
      ],
      "error": "The check implication step expects the antecedent term to be function-like."
    }
  }
}
```

## -32004 Could not parse KORE pattern

This error wraps the internal error thrown when parsing the received plain text module.

```json
{
  "jsonrpc":"2.0",
  "id":1,
  "error":  {
    "data":":21:286: unexpected token TokenIdent \\"hasDomainValues\\"\\n",
    "code":-32004,
    "message":"Could not parse KORE pattern"
  }
}
```
## -32005 Could not find module

This error wraps the internal error thrown when a module with the given name can not be found.

```json
{
  "jsonrpc":"2.0",
  "id":1,
  "error":  {
    "data":"MODULE-NAME",
    "code":-32005,
    "message":"Could not find module"
  }
}
```

## -32032 Internal server error

This error indicates an internal problem with the server implementation. Its data is not expected to be processed by a client (other than including it in a bug report).
