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
    "assume-state-defined": true,
    "cut-point-rules": ["rule1"],
    "terminal-rules": ["ruleFoo"],
    "moving-average-step-timeout": true,
    "step-timeout": 1234,
    "module": "MODULE-NAME",
    "state": {
      "format": "KORE",
      "version": 1,
      "term": {}
    },
    "log-successful-rewrites": true,
    "log-failed-rewrites": true,
  }
}
```

Optional parameters: `max-depth`, `cut-point-rules`, `terminal-rules`, `moving-average-step-timeout`, `step-timeout` (timeout is in milliseconds), `module` (main module name), `assume-state-defined` (description follows) and all the `log-*` options, which default to false if unspecified.

If `assume-state-defined` is set to `true`, the all sub-terms of `state` will be assumed to be defined before attempting rewrite rules.

_Note: `id` can be an int or a string and each message must have a new `id`. The response objects have the same id as the message._

#### Deprecated parameters

The request parameters for simplification logs are deprecated. The servers will not return simplification logs in future.

```json
{
  "params": {
    "log-successful-simplifications": true,
    "log-failed-simplifications": true
  }
}
```

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
    "data": [
      {
        "context": [
            "symbol or alias \'Lbl\'-LT-\'generatedTop\'-GT-\'\' (<unknown location>)","symbol or alias \'Lbl\'-LT-\'k\'-GT-\'\' (<unknown location>)","symbol or alias \'kseq\' (<unknown location>)","symbol or alias \'inj\' (<unknown location>)","symbol or alias \'Lbl\'UndsUndsUnds\'TESTFOO-SYNTAX\'Unds\'Stmt\'Unds\'Stmt\'Unds\'Stmt\' (<unknown location>)"
        ],
        "error": "Head \'Lbl\'UndsUndsUnds\'TESTFOO-SYNTAX\'Unds\'Stmt\'Unds\'Stmt\'Unds\'Stmt\' not defined."
      }
    ],
    "code": 2,
    "message": "Could not verify pattern"
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
* `"reason": "vacuous"`
* `"reason": "timeout"`
* `"reason": "aborted"`

and a field `state` which contains the state reached (including optional `predicate` and `substitution`), as well as a field `depth` indicating the execution depth (i.e., number of rewrite steps.

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
    "reason": "stuck",
    "logs": []
  }
}
```

#### Explanation of `reason` field and additional fields.
The `reason` field provides information about why the execution stopped.
Depending on the given `reason`, additional fields may be present.

##### `"reason": "stuck"`
Execution reached a state where no rewrite rule could be applied.
This response has no additional fields.

##### `"reason": "depth-bound"`
Execution reached the `max-depth` bound provided in the request
This response has no additional fields.

##### `"reason": "timeout"`
Execution was stopped because a rewrite step took longer than the `step-timeout` provided in the request (either in absolute time for a single step, or as a moving average value).
This response has no additional fields.

##### `"reason": "aborted"`
Execution reached a state that the server cannot handle.
The `unknown-predicate` field MAY contain a predicate that could not be decided by the server's constraint solver.

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
    "reason": "aborted",
    "unknown-predicate": {"format":"KORE", "version":1, "term":{}}
    "logs": []
  }
}
```

##### `"reason": "cut-point-rule"`
Execution was about to perform a rewrite with a rule whose label is one of the `cut-point-rules` labels/IDs of the request.  
An additional `rule` field indicates which of the `cut-point-rules` labels/IDs led to stopping.
An additional `next-states` field contains the next state (which stems from the RHS of this rule) in a singleton list.

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
    ],
    "logs": []
  }
}
```

##### `"reason": "terminal-rule"`
Execution performed a rewrite with a rule whose label is one of the `terminal-rules` labels/IDs of the request.  
An additional `rule` field indicates which of the `terminal-rule` labels or IDs led to terminating the execution:

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
    "rule": "ruleFoo",
    "logs": []
  }
}
```

##### `"reason": "vacuous"`
Execution reached a state where, most likely because of ensured side conditions, the configuration became equivalent to `\bottom`.
The `state` field contains this last configuration, no additional fields are present.

##### `"reason": "branching"`
More than one rewrite rule has applied (possibly because of splitting the state and adding branching conditions)

An additional `next-states` field contains all following states of the branch point.
```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "reason": "branching",
    "depth": 0,
    "state": <T><k> a ~> . </k> <val> X </val></T>
    "next-states": [
      {
        "term": <T><k> c ~> . </k> <val> X </val></T>,
        "predicate": #Not (X #Equals 0),
        "rule-id": "6974170fb1496dc2cae5b77afce0c12386d66ce73a4b2344c6512681ba06c70d",
        "rule-predicate": #Not (X #Equals 0),
        "rule-substitution": {...}
      },
      {
        "term": <T><k> b ~> . </k> <val> 0 </val></T>,
        "rule-id": "79cf50846fb75eb486ff134a1a00f1546aee170ae548228b79d8898c12c93d2b",
        "rule-predicate": X #Equals 0,
        "substitution": V #Equals X #And X #Equals 0 #And ...
      }
    ]
  }
}
```

(note, in the example above theconfiguation and conditions have been pretty printed for clarity. The actual response would contain a `{"format":"KORE", "version":1, "term":{...}}` JSON term.)

##### Clarifications
* It is possible that some of the `next-states` in a `branching` result have not actually taken rewrite steps. If one of the branches is stuck because of the added (branching) side condition, `next-states` will also contain this branch, with a term identical to the one in `state` and the branching condition added to the prior `predicate` from `term`.  
  Rationale: The branching should be indicated to the user. A subsequent `execute` step starting from this stuck `state` will of course immediately report `stuck`.
* `branching` results are preferred to `cut-point-rule` and `terminal-rule` results. That means, if execution reaches a branch with one of the applying rules having a label/ID from `cut-point-rules` or `terminal-rules`, the response will be `branching`.  
  Rationale: The branching information must be provided, assuming the client will re-execute on each branch.
* The `rule-predicate` term is a subterm of the `predicate` response and signals the requires clause predicate that was undecidable and thus caused branching. Note that variables inside `rule-predicate` may not always be present in the configuration, as they may have been simplified away.
* `rule-substitution` is the substitution of the internal variables of the rules LHS with terms in the configuration before the rewrite. This data is purely for diagnostic purposes and should not be used for any reasoning as it contains interal variable names from the applied rule. The `substitution` field on the other hand is returned when the backend infers a new equality for some of the variables present in the configuration, e.g. when the backend splits on the condition `X == 0`, it adds `X == 0` into the substitution field in the response.

#### Optional Logging

If any logging is enabled, the optional `logs` field will be returned containing an array of objects of the following structure:

```json
{
  "tag": "rewrite",
  "origin": "kore-rpc",
  "result": {
    "tag": "success",
    "rule-id": "7aa41f364663373c0dc6613c939af530caa55b28f158986657981ee1d8d93fcb",
  }
}

{
  "tag": "rewrite",
  "origin": "kore-rpc",
  "result": {
    "tag": "failure",
    "rule-id": "f6e4ebb55eec38bc4c83677e31cf2a40a72f5f943b2ea1b613049c92af92125c",
    "reason": "..."
  }
}
```

where `origin` is one of `kore-rpc`, `booster` or `llvm`. The order of the trace messages in the `logs` array is the order the backend attempted and applied the rules and should allow for visualisation/reconstruction of the steps the backend took. The `original-term-index` is referencing the JSON KORE format and is 0 indexed. The above traces will be emitted when `log-successful-rewrites` and `log-failed-rewrites` are set to true respectively. Not all backends may support both message types.

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
    "module": "MODULE-NAME",
    "assume-defined": false
  }
}
```

Optional parameters: `module` (main module name), `assume-defined`.

The `assume-defined` flag defaults to `false`. When set to `true`, the server uses the new simplified implication check in booster, which makes the assumption that the antecedent and consequent are bot defined, i.e. don't simplify to `#Bottom`.

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
    "code": 4,
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

If the implication holds, `satisfiable` is `true` and `condition` contains a witness, in the form of a predicate and a substitution which unifies the simplified antecedent and the consequent with existential quantifiers removed. The `condition.substitution` will contain a witnessing value for each existentially quantified variable of the RHS.

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
    },
    "logs": []
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
    "satisfiable": false,
    "logs": []
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
    "module": "MODULE-NAME",
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
    "state": {"format": "KORE", "version": 1, "term": {}},
    "logs": []
  }
}
```

## Add-module

* Allows extending the current rule-set of the RPC server by sending textual KORE definition of a module to the server.
* The server computes the SHA256 hash of the unparsed module string and saves the internalised module under this key, returning this ID in the response
* The optional `name-as-id` parameter allows the user to refer to the module by the name as well as the hashed ID.
* The IDs and original names are not disjoint for ease of implementation. the `m` pre-pended to the hash is necessary to make the name a valid kore identifier. 

### Request

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "add-module",
  "params": {
    "module": "module MODULE-NAME endmodule []",
    "name-as-id": true
  }
}
```

* `module` is a module represented in textual KORE format. The module may import modules that have been loaded or added earlier
* `name-as-id` is an optional argument which adds the module to the module map under the module name as well as the its ID. 

### Error Response:

If the textual KORE in `module` is syntactically wrong, the response will use the error code
`Could not parse pattern` with the parse error in the `data` field (also see below).

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "data": ":21:286: unexpected token TokenIdent \\"hasDomainValues\\"\\n",
    "code": 1,
    "message": "Could not parse pattern"
  }
}
```

If two dfferent modules with the same name and `name-as-id: true` are sent, the second request will fail with a `Duplicate module name` error

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "code": 8,
    "message": "Duplicate module name"
  }
}
```

However, if the modules are sent twice with `name-as-id: false` or without `name-as-id`, the second request will succeed. 
THe request will also succeed in case the same module is sent multiple times, irrespective of the value of `name-as-id`.


Other errors, for instance, using an unknown sort or symbol, will be reported with the error code
`Could not verify pattern` and a more specific error message in the `data` field.

### Correct Response:

Responds with the name of the added module if successful.

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "module": "`m<sha256_of_given_module>"
  }
}
```

The module ID `m<sha256_of_given_module>` can now be used in subsequent requests to the server by passing `"module": "m<sha256_of_given_module>"`.

## Get-model

A `get-model` request aims to find a variable substitution that satisfies all predicates in the provided `state`, or else responds that it is not satisfiable. The request may also fail to obtain an answer.

**Note that only the _predicates_ in the provided `state` are checked.**
A predicate in matching logic is a construct that can only evaluate to `\top` or `\bottom`. Most ML connectives (with the exception of `\and` and `\or`) constitute predicates.  
If the provided `state` _does not contain any predicates_, the endpoint will respond with `Unknown` (to avoid misunderstandings).

### Request:

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "get-model",
  "params": {
    "state": {"format": "KORE", "version": 1, "term": {}},
    "module": "MODULE-NAME"
  }
}
```

Optional parameters: `module` (main module name)

### Error Response:

same as for `execute`

### Correct Response:

```json
{
  "jsonrpc":"2.0",
  "id":1,
  "result":{
    "satisfiable": "Sat",
    "substitution": {"format": "KORE", "version": 1, "term": {}}
}
```

Optional fields: `substitution` (filled when `satisfiable = is-satisfiable`)

The `satisfiable` field can have the following values:
* `"satisfiable": "Sat"`:  
  The predicates can be satisfied. The  field `substitution` must be present, and provides a substitution that fulfils all predicates in the supplied `state`. Exception: if the predicates are trivially satisfied without any variable assignments, the trivial (empty) `substitution` is omitted.
* `"satisfiable": "Unsat"`:  
  The predicates are known to not be satisfiable. The `substitution` field is omitted.
* `"satisfiable": "Unknown"`:  
  The backend was unable to decide whether or not there is a satisfying substitution, or the provided tern did not contain any predicates. The `substitution` field is omitted.

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
    "code": 2,
    "message": "Could not verify pattern",
    "data": {}
  }
}
```

The kore-rpc specific error messages will use error codes in the range -32000 to -32099 and are listed for individual calls above as well as collected below for convenience.

## -32001 Cancel request unsupported in batch mode

Due to the way that cancel is implemented, we do not allow a cancel message within batch mode. This message should never occur if batch mode is not used.

## -32002 Runtime error

A catch all when the backend throws an error, e.g. an assertion violation or an IO runtime error.

This error indicates an internal problem with the server implementation. Its data is not expected to be processed by a client (other than including it in a bug report).

## -32601 Not implemented

The backend currently does not support the requested function.

## -32003 Unsupported option

With multiple backends, there might not be full feature parity between the different servers. If the current backend does support the given function but doesnt support some optional parameters, it will throw `-32003 Unsupported option` for the given parameter instead of `-32601 Not implemented`.


## 1 Could not parse pattern

This error wraps the internal error thrown when parsing the received plain text module.

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "data": ":21:286: unexpected token TokenIdent \\"hasDomainValues\\"\\n",
    "code": 1,
    "message": "Could not parse pattern"
  }
}
```

## 2 Could not verify pattern

This error wraps the internal error thrown when validating the received pattern against the loaded definition file.

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "code": 2,
    "message": "Could not verify pattern",
    "data": {
      "context": ["\\top (<unknown location>)","sort 'IntSort' (<unknown location>)","(<unknown location>)"],
      "error": "Sort 'IntSort' not defined."
    }
  }
}
```

## 3 Could not find module

This error wraps the internal error thrown when a module with the given name can not be found.

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "data": "MODULE-NAME",
    "code": 3,
    "message": "Could not find module"
  }
}
```

## 4 Implication check error

This error wraps an error message from the internal implication check routine, in case the input data is inconsistent or otherwise unsuitable for the check.

```json
{
  "jsonrpc":"2.0",
  "id":1,
  "error": {
    "code": 4,
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


## 5 Smt solver error

Error returned when the SMT solver crashes or is unable to discharge a goal.

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "code": 5,
    "message": "Smt solver error",
    "data": {
      "term": {
        "format": "KORE",
        "version": 1,
        "term": {}
      },
      "error": "(incomplete (theory arithmetic))",
    }
  }
}
```

## 6 Aborted

## 7 Multiple states

The two errors above indicate that the execute endpoint ended up in an erroneous/inconsistent state and the returned error message is should be included in the bug report.

# 8 Invalid module

The module could not be parsed or is invalid (e.g. contains new symbols)

# 9 Duplicate module name

A module with the same name is already loaded on the server
