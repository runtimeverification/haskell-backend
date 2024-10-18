Booster: the fast symbolic rewrite engine for K
===============================================

This document is a detailed description of the Booster --- the fast rewrite engine implementing the [Kore JSON RPC](./2022-07-18-JSON-RPC-Server-API.md) protocol.

Original Booster design: https://github.com/runtimeverification/hs-backend-booster/issues/3

The Haskell backend booster started at inception following a few basic concepts for symbolic execution and reasoning:

- Symbolic execution is _modular_, and so can be broken down into primitives that can be exposed over an API,
- Symbolic execution can be improved _incrementally_ by replacing slower algorithms with simple (but fast and incomplete) algorithms that can detect when they are insufficient,
- The majority of symbolic execution is very _simple_ (what we call "bulk" symbolic execution), with small bits of more tricky reasoning sprinkled throughout, and
- The vast majority of the time doing symbolic reasoning is spent _failing_ to apply rules (rewrite or equational), and so the failure cases should fall out as fast as possible.

To take advantage of this design, we first broke Kore (the original symbolic reasoning engine, or "old Haskell backend") into three endpoints:

- The `execute` endpoint, which takes care of doing bulk symbolic execution,
- The `simplify` endpoint, which takes care of applying equational simplifications to states as exstensively as possible, and
- The `implies` endpoint, which takes care of determining if one state is subsumed into another (and returning the evidence of it when there is subsumption).

By breaking Kore into these three components, we were able to focus on improving each one independently with faster algorithms for each.
Note that the overall goal was still to have a _Reachability_ prover, for which all three endpoints are necessary.
Kore directly implemented a Reachability prover, but the new booster does not, instead it relies on `pyk` to implement the Reachability logic on top of the symbolic reasoning API.
This allows more flexibility in future design, because the actual properties being proved only need to be handled at the `pyk` level, while the booster can focus purely on the symbolic reasoning components.

A key part of how we approached designing the booster was to ensure that we maintained the completeness of reasoning that Kore provided, while getting any performance benefits of the booster too.
To achieve this, we implemented the _proxy_ server, which would take each API call (to `execute`, `simplify`, or `implies`) and attempt it with the booster first; if the booster failed then it would delegate the call to Kore afterwards.
The initial implementation of the proxy was to _always_ delegate calls to Kore, basically assuming that the booster could not handle any inputs.
Over time, as the booster was able to pass more tests and handle more inputs, the proxy server delegated more work to the booster.

To date, the most work has been put into making the `execute` endpoint of the booster as complete and performant as possible, as that is where the bulk of time on long-running proofs is spent.
Necessarily, as part of the `execute` endpoints reasoning, simplification reasoning of the booster needs to be improved too, which means the `simplify` endpoint has improved as well.
Only a very rudimentary `implies` endpoint has been implemented, to handle most of the failure cases as fast as possible, and usually the more complicated reasoning is still delegated to the Kore `implies` endpoint.
