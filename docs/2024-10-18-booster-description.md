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

We now describe in more detail the implementation of Booster, focusing on the following high-level tasks:
- rewriting, which underpins the `execute` endpoint;
- applying equations, which underpins the `simplify` endpoint and is also used in certain key points in the `execute` endpoint;
- definition and state internalisation, i.e. the process of transforming the external `KoreJson` terms of the semantics definition and input states into Booster's internal data structures.

## [Rewriting](#rewriting)

Once the server is started with the rules for a given semantics, the execute end-point expects a configuration composed of a `Term`, representing the state of execution in a given semantics, along with boolean `Predicate`s/constraints imposed upon any symbolic parts of the state. Given this state, the server will apply semantic rules to the configuration, until either:

* no more rules apply
* a user specified break point is reached, based on a specific semantic rule or specified depth
* a branch occurs, i.e. more than one rule applies
* the booster cannot decide if a rule should apply

The execution can roughly be divided into two phases. The rewrite rule application phase and the simplification phase. Unlike the old backend, which is much more aggressive in applying simplification and function rules, the booster tries to apply rewrite rules as long as it can. Once it reaches a point where unification fails due to some part of the configuration containing un-evaluated functions which need to match a concrete value in the rule, the booster will run the simplifier on the current configuration to try to evaluate any function calls inside the configuration before trying to re-write again. This strategy avoids the costly simplifier running after each rewrite, but can be a double edged sword as the booster often ends up building a big stack of unevaluated functions in parts of the configuration. This usually happens in rules operating on the stack/heap/memory cells of a particular semantics, which often functionally update the state from previous configuration by calling an append/upsert/etc. function. In certain instances, the configuration ends up growing at an enormous rate as these thunks build up and can cause failure when the simplifier runs out of memory, trying to simplify such a huge configuration term. To prevent this from happening, the booster proxy contains a simple strategy which allows the user to force the simplification phase to be triggered every _n_ rewrite steps  (_n_ can be specified via a flag at server startup).

For an overview of what happens when an execute request is received, see the diagram bellow. We give further details of some of the steps/states in this diagram, in the following sections.

```
                                   Receive execute request   ──────────────────────────┐
                                                                                       │
                                             │                                         │
                                             ▼                                         ▼

                            Internalise KoreJSON into pattern P           Unsupported KoreJSON pattern

                                             │                                         │
                                             ▼                                         ▼

                                       Check P /= _|_                           Return an error

                                             │
                                             │   ┌──────────────────────────────────────────────────────────────────────────────────────────────────┐
┌────────────────────────────────────────┐   │   │                                                                                                  │
│                                        ▼   ▼   ▼                                                                                                  │
│                                                                                                                                                   │
│         ┌────────────────────────────  Apply rule  ◄───────────────────────────────────────────────────────────────────────────────────────────┐  │
│         │                                                                                                                                      │  │
│         │                                    │                                                                                                 │  │
│         │                                    └─────────────┐                                                                                   │  │
│         ▼                                                  ▼                                                                                   │  │
│                                                                                                                                                │  │
│  Rewrite aborted            ┌────────────────────  Rewrite finished  ─────────────────────────┐                                                │  │
│                             │                                                                 │                                                │  │
│         │                   │                               │                                 │                                                │  │
│         │                   │                               │                                 │                                                │  │
│         ▼                   ▼                               ▼                                 ▼                                                │  │
│                                                                                                                                                │  │
│  Return aborted       No rules apply                 Rewrite to P'  ───┐                  Rewrite to PS ─────────────────┬───────┐             │  │
│                                                                        │                                                 │       │             │  │
│                             │                           │              │                    │      │                     │       │             │  │
│                             │                           │              │                    │      └──────────┐          │       │             │  │
│                             │                           ▼              ▼                    ▼                 ▼          │       ▼             │  │
│                             │                                                                                            │                     │  │
│                             │                         P' == _|_    P' /= _|_           /\ PS == _|_      PS simplify to  │   PS simplify to  ──┘  │
│                             │                                                                                   []       │      single P'         │
│              ┌──────────────┼─────────────┐               │           │ │                   │                            │                        │
│              │              │             │               │           │ │                   │                   │        │                        │
│              ▼              ▼             ▼               │           │ │                   │                   │        └───────┐                │
│                                                           │           │ │                   │                   │                ▼                │
│          Does not     Simplified      Simplifies          │  ┌────────┼─┼───────────────────┘                   │                                 │
│          simplify      already                            │  │        │ │                                       │          PS simplify to         │
│                                                           │  │        │ │                                       │                PS'              │
│              │              │             │               │  │        │ │                                       │                                 │
│              │              │             │               ▼  ▼        │ │                                       │                 │               │
│              │              │             │                           │ └─────────────────┐                     │                 ▼               │
│              │              │             │        Return vacuous P   │                   │                     │                                 │
│              │              │             │                           │                   │                     │         Return branching        │
│              │              │             │                           │                   │                     │                                 │
│              └───────┐      │             │                           ▼                   ▼                     │                                 │
│                      ▼      ▼             │                                                                     │                                 │
│                                           │                    Depth/rule bound       Unbounded  ───────────────┼─────────────────────────────────┘
│                     Return stuck P        │                                                                     │
│                                           │                           │                                         │
│                            ▲              │                           │                                         │
│                            │              │                           │                                         │
└────────────────────────────┼──────────────┘                           ▼                                         │
                             │                                                                                    │
                             │                                    Return simplified P'                            │
                             │                                                                                    │
                             │                                                                                    │
                             └────────────────────────────────────────────────────────────────────────────────────┘
```

### [Single Rewrite Rule](#rewriting-apply-single-rule)

[applyRule](https://github.com/runtimeverification/haskell-backend/blob/3956-booster-rewrite-rule-remainders/booster/library/Booster/Pattern/Rewrite.hs#L329)

Steps to apply a rewrite rule include:

- Matching with the rule, i.e. does the current configuration looks like a rule's left-hand side. Successful matching produces a substitution `RULE_SUBSTITUTION`, assigning the left-hand side rule variables with the stuff from the configuration. See [#rule-matching](#rule-matching) for more details.
- Checking the rule's requires clause. Unclear conditions may produce a remainder predicate, which affects the wider rewriting step process. See [#checking-requires](#checking-requires).
- Checking the rule's ensures clause, and extracting the possible new substitution items from the ensured constraints. See [#checking-ensures](#checking-ensures).
- Constructing the final rewritten configuration.

The rule application routine may reach an exception condition, in which case the whole rewriting step is aborted, i.e. no other rules will be attempted, causing a full-stop.
These **abort conditions** include:
- indeterminate matching of the rule's left-hand side and the current configuration
- internal error during matching, likely indicating a bug in the matcher
- a non-preserving-definedness rule, i.e. a rule which has partial symbols on the RHS and no `preserves-definedness` attribute
- unknown constraint in `ensures`

#### [Matching the configuration with the rule's left-hand side](#rule-matching)

See the [Booster.Pattern.Match](https://github.com/runtimeverification/haskell-backend/blob/3956-booster-rewrite-rule-remainders/booster/library/Booster/Pattern/Match.hs#L48) module, specifically the [matchTerms](https://github.com/runtimeverification/haskell-backend/blob/3956-booster-rewrite-rule-remainders/booster/library/Booster/Pattern/Match.hs#L132), [match](https://github.com/runtimeverification/haskell-backend/blob/3956-booster-rewrite-rule-remainders/booster/library/Booster/Pattern/Match.hs#L171) and [match1](https://github.com/runtimeverification/haskell-backend/blob/3956-booster-rewrite-rule-remainders/booster/library/Booster/Pattern/Match.hs#L191) functions
- rules are indexed by the head symbol of the `<k>` cell (or other index-cells), i.e. we only try the rules that have the same head symbol that the configuration
- rules can fail matching, usually that means that the rule and the configuration have different constructor symbols or domains values in some cells.
  This means that the rule does not apply and we can proceed to trying other rules.
- rule matching can be indeterminate. We really do not want this to happen, as it will abort rewriting and cause a fallback to Kore (or a full-stop of using the `booster-dev` server).
  Common cases include unevaluated function symbols. See [match1](https://github.com/runtimeverification/haskell-backend/blob/3956-booster-rewrite-rule-remainders/booster/library/Booster/Pattern/Match.hs#L191) and look for `addIndetermiante` for the exhaustive list.

#### [Checking `requires` --- the rule's pre-condition](#checking-requires)

-   now we have to check the rule's side-condition, aka the `requires` and `ensures` clauses. Booster represents the `requires` and `ensures` clauses as a set of boolean predicates, constituting the conjuncts, i.e. they are implicitly connected by `_andBool_`, but Booster works with them independently, which makes filtering, de-duplication and other operations straightforward. Write your requires clauses in CNF!
-   the requires clause check is encapsulated by the [checkRequires](https://github.com/runtimeverification/haskell-backend/blob/3956-booster-rewrite-rule-remainders/booster/library/Booster/Pattern/Rewrite.hs#L496) function in applyRule. It will:
    -   substitute the rule's requires clause with the matching substitution
    -   check if we already have any of the conjuncts verbatim in the pattern's constrains. If so, we filter them out as known truth
    -   simplify every conjunct individually by applying equations. This is where Petar is welcome to take over with his 4 hours workshop on simplifications.
    -   filter again
    -   if any clauses remain, it's time to fire-up Z3 and check them for validity.
        -   some rule will be rejected at that point, as their pre-condition P (the `requires` clause) is invalid, which means that the rule is applicable statically, but the dynamic conditions makes it inapplicable.
        -   some rules may have an indeterminate pre-condition P, which means that both P and its negation are satisfiable, i.e. the solver said (SAT, SAT) for (P, not P).
            In this case we can apply this rule conditionally, but add P into the path condition.
            We effectively do the same we cannot establish the validity of P due to a solver timeout, i.e. we add the predicate as an assumption. This may potentially lead to a vacuous branch.
        -   some rules will have a valid requires clause, which means they definitely do apply and we do need to add anything else into the path condition as an assumption.

#### [Checking `ensures` --- the rule's post-condition](#checking-ensures)


### [Single Rewriting Step](#rewriting-single-step)

### [Iterating Rules](#rewriting-many-steps)

Successful rule application does not trigger pattern-wide simplification, i.e. very far and make many steps without simplifying the pattern even ones.
We do need to perform a pattern-wide simplification if we hit any of the rule application abort conditions of the [single rule application algorithm](#rewriting-apply-single-rule).
That allows us to leverage function and simplification equations to possibly simplify away the cause of the abort.
See the [simplifier](#equations) section for details on how simplification and function evaluation is performed.
After one round of pattern-wide simplification, we re-attempt rewriting and continue if progress has been made; otherwise we stop completely and return an aborted state.

## [Applying equations: function evaluation and simplification](#equations)

### [Single Equation](#equations-single-rule)
