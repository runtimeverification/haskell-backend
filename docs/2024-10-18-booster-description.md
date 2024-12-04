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

[applyRule](https://github.com/runtimeverification/haskell-backend/blob/master/booster/library/Booster/Pattern/Rewrite.hs#L329)

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

See the [Booster.Pattern.Match](https://github.com/runtimeverification/haskell-backend/blob/master/booster/library/Booster/Pattern/Match.hs#L48) module, specifically the [matchTerms](https://github.com/runtimeverification/haskell-backend/blob/master/booster/library/Booster/Pattern/Match.hs#L132), [match](https://github.com/runtimeverification/haskell-backend/blob/master/booster/library/Booster/Pattern/Match.hs#L171) and [match1](https://github.com/runtimeverification/haskell-backend/blob/master/booster/library/Booster/Pattern/Match.hs#L191) functions
- rules are indexed by the head symbol of the `<k>` cell (or other index cells), i.e. we only try the rules that have the same head symbol that the configuration
- rules can fail matching, usually that means that the rule and the configuration have different constructor symbols or domains values in some cells.
  This means that the rule does not apply and we can proceed to trying other rules.
- rule matching can be indeterminate. We really do not want this to happen, as it will abort rewriting and cause a fallback to Kore (or a full-stop of using the `booster-dev` server).
  Common cases include unevaluated function symbols. See [match1](https://github.com/runtimeverification/haskell-backend/blob/master/booster/library/Booster/Pattern/Match.hs#L191) and look for `addIndetermiante` for the exhaustive list.

#### [Checking `requires` --- the rule's pre-condition](#checking-requires)

If matching is successful, we now we have to check the rule's side-condition, aka the `requires` and `ensures` clauses. Booster represents the `requires` and `ensures` clauses as a set of boolean predicates, constituting the conjuncts. The are implicitly connected by `_andBool_`, but Booster works with them independently, which makes filtering, de-duplication and other operations more straightforward. Write your requires clauses in the conjunctive normal form!

The `requires` clause represents the logical "guard" that may impose constraints on the variables appearing on the left-hand side of the rule, thus allowing to formulate dynamic conditions of the rule's applicability.

The requires clause check is encapsulated by the [checkRequires](https://github.com/runtimeverification/haskell-backend/blob/master/booster/library/Booster/Pattern/Rewrite.hs#L496) function defined in the `where`-clause of `applyRule`. It will:
1. substitute the rule's requires clause with the matching substitution
2. check if we already have any of the conjuncts verbatim in the pattern's path condition (`PC`). If so, we filter them out as known truth
3. simplify every conjunct individually by applying equations. This is morally equivalent to sending every conjunct as to the `"simplify"` endpoint and will use the same code path, bypassing internalisation.
4. check again whether any of the, now simplified, conjuncts  is present verbatim in the path condition
5. if any clauses remain, check all conjuncts together with Z3 for validity given the path condition.
    - some rule will be rejected at that point, as their pre-condition `P` (the `requires` clause) is false given `PC`, which means that the rule is applicable statically, but the dynamic conditions makes it inapplicable.
    - some rules may have an indeterminate pre-condition `P`, which means that both `PC /\ P` and `PC /\ not P` are `SAT` in the solver, i.e., neither `P` nor  `not P` are implied by `PC`
      - in this case we can apply this rule conditionally, but add `P` into the path condition We will call `not P` the _remainder condition_ of this rule and keep track of it too
        We effectively do the same if we cannot establish the validity of P due to a solver timeout, i.e. we add the predicate as an assumption. This may potentially lead to a vacuous branch as we discover more conditions further into the rewriting process.
    -   some rules will have a valid requires clause, i.e., `PC => P`, which means they definitely apply and we do not need to add anything else into the path condition as an assumption.

See the [Booster.SMT.Interface](https://github.com/runtimeverification/haskell-backend/blob/master/booster/library/Booster/SMT/Interface.hs) module to learn more about how `Predicate`s are checked for satisfiable and validity using Z3.

Bottom line:
- if `requires` is found to be false, we do not apply the rule, just as if it didn't even match;
- otherwise, i.e. `requires` is either valid or indeterminate (remember, we are keeping track of the remainder), we can proceed to the next and final step

#### [Checking `ensures` --- the rule's post-condition](#checking-ensures)

The `ensures` clause of the rule represents:
- the rule's post-condition, which must be valid in order for the rule to be applicable (there is a nuance to that statement, which we will discuss at the end of the section)
- the rule's effect on the path constraint (aka constraints, aka known truth) of the current pattern and its substitution

The `ensures` clause has additional power compared to the `requires` clause, as it may impose constrains not only on the left hand-side variables (like the `requires` clause), but also on the right hand-side variables of the rule, known as `?`-variables or existential variables.

The `ensures` check is in many ways similar to the `ensures` check, but with some important differences. See the `checkEnsures`[https://github.com/runtimeverification/haskell-backend/blob/master/booster/library/Booster/Pattern/Rewrite.hs#L610] function.


### [Single Rewriting Step](#rewriting-single-step)

To take a rewriting step from a `Pattern` means to attempt all applicable rewrite rules at that pattern, and return one of the following results:

- stuck rewrite, no rules apply
- trivial rewrite, rewritten state is vacuous because the `ensures` clause evaluates to false
- aborted rewrite, see the [RewriteFailed](https://github.com/runtimeverification/haskell-backend/blob/master/booster/library/Booster/Pattern/Rewrite.hs#L740) datatype for the possible reasons
- rewriting finished, max depth reached
- rewriting finished, terminal rule
- rewriting finished, cut-point rule
- branch, several rules apply

#### Rewrite rule priorities and remainder predicates

The K Framework supports a powerful feature of assigning priorities to rewrite rules, which allows better structuring of the semantics.

When Booster applies rewrite rules, they are grouped by priority. The group with the higher priority applies first, and all rules are treated equally within the group.

During symbolic execution, we keep track of the current path condition --- a conjunction of logical constraints that specify an equivalence class of concrete execution states. In order to prevent state explosion, it is important to only create new symbolic states that are feasible. Priority groups enable a additional mechanism for that by enabling the semantics implementer to partition rules into complete groups, and only applying lower-priority rules under the conditions where higher-priority groups are not applicable.

A priority group of rules gives rise to a group **coverage condition**, which is defined as a disjunction of the requires clauses of the rules in the group. If the coverage condition is valid, it means that no other rules can possibly apply. The negation of the coverage condition is called the group's **remainder condition**. If the remainder condition is unsatisfiable, then the coverage condition is valid, and the group is complete.

When applying rewrite rules, Booster will take note of any indeterminate rule conditions and use them to construct the groups remainder conditions:
- when checking the `requires` clause of a rule, we compute the remainder condition `RULE_REM` of that attempted, which is the semantically-checked subset of the required conjuncts `P` which *unclear* after checking its entailment form the pattern's constrains `PC`, meaning that (PC /\ P, PC /\ not P) is (SAT, SAT) or any of the two queries were UNKNOWN
- if that remainder is not empty, we return it's *negation* together with the result
- when we are finished attempting a *priority group* of rules, we collect the negated remainder conditions `not RULE_REM_i` and conjunct them. This the groups remainder condition `GROUP_REM == not RULE_REM_1 /\ not RULE_REM_2 /\ ... /\ not RULE_REM_n`
- At that point, we need to check `GROUP_REM` for satisfiablity.
  - **If the `GROUP_REM` condition is UNSAT, it means that this group of rules is *complete***, meaning that no other rule can possibly apply, and we do not need to even attempt applying rules of lower priority. This behaviour is the **primary contribution of this PR**.
  - Otherwise, if it is SAT or solver said UNKNOWN, it means that this group of rules is not complete, i.e. it does not cover the whole space of logical possibility, and we need to construct a remainder configuration, and continue attempting to apply other rules to it. If no rules remain, it means that we are stuck and the semantics is incomplete. This PR does not implement the process of descending into the remainder branch. **Booster with this PR will abort on a SAT remainder**.

This behaviour is active by default in `booster-dev` and can be enabled in `kore-rpc-booster` with the flag `--fallback-on Aborted,Stuck` (the default is `Aborted,Stuck,Branching`). Note that with the default reasons, the behaviour of `kore-rpc-booster` is functionally the same, but operationally slightly different: In `Proxy.hs`, Booster may not return `Branching`, and the fallback logic will confirm that Kore returns `Branching` as well, flagging any differences in the `[proxy]` logs (see [Proxy.hs#L391](https://github.com/runtimeverification/haskell-backend/blob/master/booster/tools/booster/Proxy.hs#L391)).

Note:
a naive algorithm to compute the remainder conditions would be: after applying a group of rules, take their substituted requires clauses, disjunct and negate. However, this yields a non-minimal predicate that was not simplified and syntactically filtered, potentially making it harder for the SMT solver to solve. The algorithm described above and implemented in this PR re-uses the indeterminate results obtained while applying individual rules and simplifying/checking their individual requires clauses. This logic has been originally proposed by Sam in https://github.com/runtimeverification/haskell-backend/pull/3960.

See [remainder-predicates.k](https://github.com/runtimeverification/haskell-backend/blob/master/booster/test/rpc-integration/resources/remainder-predicates.k) and [test-remainder-predicates](https://github.com/runtimeverification/haskell-backend/blob/master/booster/test/rpc-integration/test-remainder-predicates) for a series of integrations tests that cover the behaviour of `booster-dev` and `kore-rpc-booster`.

### [Iterating Rules](#rewriting-many-steps)

Successful rule application does not trigger pattern-wide simplification, i.e. rewriting can proceed very far and make many steps without simplifying the pattern even once.
We do need to perform a pattern-wide simplification if we hit any of the rule application abort conditions of the [single rule application algorithm](#rewriting-apply-single-rule).
That allows us to leverage function and simplification equations to possibly simplify away the cause of the abort.
See the [simplifier](#equations) section for details on how simplification and function evaluation is performed.
After one round of pattern-wide simplification, we re-attempt rewriting and continue if progress has been made; otherwise we stop completely and return an aborted state.

## [Applying equations: function evaluation and simplification](#equations)

The simplification code path is used at two different points of the execution, as well as being exported as a separate simplify JSON RPC endpoint. The simplification procedure underpinning all of these use-cases is largely the same and comprises of two main simplifiers, the concrete and symbolic one.

Concrete function evaluation is handled by the LLVM backend and thus requires the semantics to be written in such a way, so as to be able to build both the kore definition used by the haskell backend, as well as the LLVM kore definition. The booster relies on the LLVM version of a semantics, compiled as a dynamic library, which is loaded when the server starts. During simplification, the term is traversed bottom up and any concrete sub-terms are sent to he LLVM backend to be evaluated.

The symbolic parts of a term are handled directly by the booster. Similarly to rewrite rules, function rules may also have side conditions. As a result, the simplifier may have to recurse into evaluating whether the side-condition of a function/simplification rule evaluates to true/false before successfully rewriting the term. At the moment, the evaluation strategy is hard-coded in the booster, and it is generally is the following:
- traverse the term top-down once and apply LLVM simplifications to the concrete sub-terms. It is essential to discover the concrete terms top-down and thus track the concreteness of sub-terms with attributes. By doing that, we make sure that we send a few big terms to the LLVM backend and not many small terms, thus minimising the overhead.
- traverser the term bottom-up, applying equations at every level until we make progress with at least one equation;
- when applying equations, prefer functions, and only apply simplifications when function do not produce a result anymore, i.e. no functions apply.

**TODO**: discuss the abort conditions of function vs. simplifications. In short, simplifications are optional, and functions are mandatory, i.e. we abort if a function equation produces an indeterminate match or a function condition is indeterminate.
**TODO**: discuss the process of applying a single equation.
**TODO**: discuss caching and how it's implemented in Booster.


## [Definition internalisation and pre-processing](#internalisations)

Booster takes a `definition.kore`, parses it, computes term indices, puts rules in several different buckets, infers definedness of some rules.

**TODO**: expand on the topics listed above
**TODO**: specifically, talk in detail about the `Term` datatype and `TermAttributes` datatype, how they are used to compare terms. Discuss the pattern synonym-based smart constructors.
**TODO**: it's appropriate to discuss the `"add-module"` endpoint here as well
