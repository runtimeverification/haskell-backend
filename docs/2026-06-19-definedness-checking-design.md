# Definedness checking in Booster — static vs dynamic, and the right obligation

Status: design exploration, 2026-06-19.
This document describes how `master` checks definedness today (§2), a proposed redesign (§3), the soundness question it raises (§4–§7), and a synthesis resolving it (§8) from three research threads (matching/reachability-logic literature, booster git history, in-repo docs).
Resolution: the implication `#Ceil(LHS) → #Ceil(RHS)` ("preserves definedness"), read in assume-defined mode, is the correct obligation for symbolic execution — see §8.

This document works out *how Booster should decide that applying an equation/simplification rule is sound with respect to definedness*, statically (at load) and dynamically (at rule-application time).
It is motivated by KEVM's recurring definedness fallbacks: Booster declines a simplification that involves a partial symbol and falls back to the complete (but slow) Kore engine, even in cases where the rule is in fact sound to apply.

## 1. Background: what "definedness" buys us

Booster rewrites/simplifies terms by applying equations `LHS = RHS requires P`.
Some symbols are *partial* (`[function]`, not `[total]`): an application like `X /Int Y` or `#newAddr(A,B)` may denote nothing (⊥) for some arguments.
Applying an equation that involves a partial symbol can be unsound unless we know the relevant definedness conditions hold.
Booster's conservative stance today: if a rule mentions a partial symbol it cannot statically discharge, it *declines* (aborts) and the proxy falls back to Kore.
A large fraction of KEVM's Booster→Kore fallbacks are exactly these definedness declines.

## 2. The current implementation on `master`

It helps to separate what is computed once at load, what is stored on the rule, and what is computed on every rule application.

**Computed once, at load (internalisation):**

- `notPreservesDefinednessReasons` — a *blame list* of the partial-symbol names found in the rule, computed for every rule kind.
  Rewrite and function rules scan the **RHS only** (`booster/library/Booster/Syntax/ParsedKore/Internalise.hs:828`).
  Simplification rules scan **both LHS and RHS** (`Internalise.hs:892`, comment: *"checking the lhs term, too, as a safe approximation (rhs may introduce undefined, lhs may hide it)"*).
  It is a list of symbol *names* — a yes/no-with-blame flag, not a condition.
- The static ceil analysis `computeCeilsDefinition` (`Booster/Definition/Ceil.hs`, PR #402), run unconditionally at startup (`Server.hs:245`, `booster-dev/Server.hs:79`) over the **rewrite theory only**.
  For each flagged rewrite rule it computes the residual `simplify( computeCeil(rhs) ∖ computeCeil(lhs) ∖ computeCeil(requires) )` — i.e. `#Ceil(RHS)` under `#Ceil(LHS) ∧ requires` (this is "Model A" of §4).

**Stored on the rule:**

- The blame list, in `computedAttributes.notPreservesDefinednessReasons`.
- The static ceil analysis result is stored **only as a mutation** of the rule: when the computed residual is empty, the rule is rewritten to `preserving = True` and the blame list is cleared, so the rule then applies freely.
  The residual itself is **not** stored — `RewriteRule` has no field for it — and when the residual is **non-empty it is discarded** (logged as a `ComputeCeilSummary` only; `newRule = Nothing`; the comment at `Ceil.hs:125` notes that attaching it is future work).
- `simplifications` and `functionEquations` get **no** ceil analysis at all, so for them only the blame list is stored.

**Computed at every rule / equation / simplification application:**

- Nothing definedness-related is recomputed.
  The gate (`ApplyEquations.hs:716`) is a single read of the stored blame list:
  `unless (null rule.computedAttributes.notPreservesDefinednessReasons) $ throwE … RuleNotPreservingDefinedness`.
  Any rule still flagged after the load-time analysis is **rejected outright** — there is no runtime discharge of any kind.
  `RuleNotPreservingDefinedness` routes through the `ResultHandler`: function equations → `abort`, simplification equations → `continue` (skip to the next rule), and in practice the proxy falls back to Kore.

**Consequence.**
Rewrite rules can be cleared by the static analysis; simplification and function rules never are.
So a simplification rule declines whenever it carries any partial symbol on either side.
The dominant KEVM definedness fallbacks (`#newAddr`, `_<<Int_`, `#lookup`, `#WordPack`) are exactly such simplification rules — rejected by Booster and rescued by Kore.

## 3. The proposed redesign

**(i) Load time.**
Compute the rule's definedness obligation as a `#Ceil` expression, simplify it, and *attach the residual* to the rule.
If it simplifies to `#Top`, the rule provably preserves definedness and needs no runtime check.
Otherwise the residual (some leftover `#Ceil(...)` conjunction) is stored on the rule.

**(ii) Application time.**
After a successful match (for the rule kind in hand), if the rule carries a residual definedness condition: substitute the match σ into it, simplify the terms inside, and check whether the result is *trivially defined* (built only from total functions, constructors, domain values, variables — the structural check of §6).
If trivially defined → continue applying the rule.
If not → abort with *indeterminate*, letting the surrounding rule-application logic decide what to do next.

This is largely an *extension of the static `Ceil.hs` analysis described in §2*: run it over `simplifications` and `functionEquations` (not just the rewrite theory), and — crucially — **stop discarding the non-empty residual** (`Ceil.hs:125`), storing it on the rule instead.
It differs from `master` in that load produces and **stores** a symbolic residual predicate (not just a discarded symbol-name blame list), the runtime check looks at the **real obligation** rather than rejecting any flagged rule outright, and discharge is **simplify-then-check-defined / SMT** rather than an unconditional decline.

## 4. The central question: which obligation?

Two candidate obligations for "safe to rewrite the matched `LHS[σ] → RHS[σ]`":

- **Model A — preserves-definedness (the implication).**  `#Ceil(LHS) #Implies #Ceil(RHS)`.
  "If the thing we are rewriting is defined, the result is defined."
  Rationale: symbolic execution / reachability logic *starts from a defined state*, and if every rule **preserves** definedness (never turns a defined state undefined) then, by induction, every reachable state is defined.
  Under this model `#Ceil(LHS)` holds **by assumption** at every redex we simplify, so the only new obligation is `#Ceil(RHS)`.
  Where the implication cannot be discharged statically, discharge it dynamically using the substitution and path condition available at that point.

- **Model B — conservative / local (the conjunction).**  `#Ceil(LHS) #And #Ceil(RHS)`.
  "Rewriting is sound only where both the redex and the result are defined," making **no** global assumption that the redex is defined.
  Equivalent to: discharge `#Ceil` of every maximal partial sub-term on *both* sides.

They differ in exactly one assumption: **may we assume `#Ceil(LHS)` for the matched redex?**
Model A says yes (the configuration is defined, so its subterms are); Model B says no.

Worked examples (let `<=Int` be total, `<<Int` / `/Int` partial, `#newAddr` partial):

| rule | `#Ceil(LHS) ⟹ #Ceil(RHS)` (A) | `#Ceil(LHS) ∧ #Ceil(RHS)` (B) | comment |
|---|---|---|---|
| `0 <=Int #newAddr(A,B) => true` | `#Ceil(#newAddr(A,B)) → #Top` = **#Top** | `#Ceil(#newAddr(A,B))` | partial symbol in **LHS**, RHS total |
| `0 <=Int (X <<Int Y) => true`   | `(Y>=0) → #Top` = **#Top**            | `Y>=0`                  | partial symbol in **LHS** |
| `X => 1 /Int X`                 | `#Top → (X=/=0)` = **X=/=0**          | `X=/=0`                 | partial symbol introduced in **RHS** |

Key observation: A and B agree when the partiality is *introduced in the RHS*, but diverge when it is *in the matched LHS*.
For the LHS cases, Model A declares the rule definedness-preserving (residual `#Top`, apply freely), while Model B demands a runtime `#Ceil` discharge.
The KEVM declines are overwhelmingly LHS cases — so under Model A they would simply be recognised as preserving definedness at load and applied with no runtime work, and today's declines are an artefact of the conservative "any partial symbol ⇒ bail" approximation (`master` never even computes the implication for simplification rules).

If Model A is the correct soundness model, then:
- the redesign's load-time step should compute and simplify `#Ceil(LHS) ⟹ #Ceil(RHS)`;
- most KEVM declines vanish at load with no runtime discharge needed;
- the only rules needing a *runtime* residual check are those where the implication does not statically reduce to `#Top` (typically RHS-introduced partiality, e.g. `1 /Int X`), and there the residual is discharged against the path condition / σ.

If Model B is correct (no assume-defined), the implication is unsound for the LHS-hiding case and the obligation must be the conjunction.

This is the question §8 settles.
It hinges on the semantics of symbolic execution in matching/reachability logic: is the configuration assumed defined, and does `#Ceil(config) → #Ceil(subterm)` hold for the subterms we simplify (i.e. is ordinary symbol application strict w.r.t. ⊥)?

## 5. Static vs dynamic, restated

- **Static (load):** for each rule, build the definedness obligation (A or B per §4), simplify with the `#Ceil` machinery (`booster/library/Booster/Definition/Ceil.hs`) and totality information.
  Outcome is either `#Top` (no check ever needed) or a residual predicate attached to the rule.
  No σ and no path condition are available yet, so conditional obligations remain symbolic.
- **Dynamic (apply, post-match):** substitute σ into the residual, simplify, and discharge — by structural trivially-defined check, by reduction to a domain value, and/or by SMT against the known constraints / path condition.
  Accept → apply the rule; fail → abort indeterminate and let the caller (function-equation vs simplification vs rewrite vs implies) decide.

## 6. The "trivially defined" checker

`#Ceil(t) = #Top` when `t` is built entirely from total functions, constructors, domain values, and variables (a variable denotes a defined element of its sort; ordinary application of total/constructor symbols to defined args is defined).
Operationally this is a structural check: `t` has no maximal sub-term rooted at a partial (`Function Partial`) symbol — a recursion over `isDefinedSymbol` (`booster/library/Booster/Pattern/Util.hs:200`).
The same check serves both the load-time residual computation and the runtime accept-test.
(Settled in §8: a free variable is always `#Ceil`-true — the matching-logic `∀x. ⌈x⌉` axiom — so variables need no special handling beyond freshly-introduced existentials.)

## 7. Open research questions (driving the three threads)

These drove the research; §8 answers them.

1. **Literature (matching/reachability logic).**
   In reachability-logic symbolic execution, is the configuration assumed defined?
   Is `#Ceil(LHS)` assumable when simplifying a subterm of a defined configuration (does `#Ceil(C[t]) → #Ceil(t)` hold; is application strict w.r.t. ⊥)?
   What is the standard "preserves definedness" / equation-application soundness obligation — implication, conjunction, or other?
2. **Git history (haskell-backend + the former hs-backend-booster repo).**
   How did `notPreservesDefinednessReasons`, the `preserves-definedness` attribute, the static `#Ceil` analysis, and `assumeDefined` evolve?
   What rationale was recorded for the conservative check vs an assume-defined model?
3. **In-repo docs.**
   What do the existing docs say about definedness, `#Ceil`, totality/partiality, `assumeDefined`, and the assumptions made about the configuration being defined?

## 8. Synthesis: how to check definedness safely (static + dynamic)

Synthesised from three research threads: matching/reachability-logic literature, the booster git history (incl. the former `hs-backend-booster` repo), and the in-repo docs.
Bottom line up front: **Model A is the correct obligation for symbolic execution**, provided it is read in "assume-defined" mode — which is precisely the mode symbolic execution operates in, and the mode the complete engine (Kore) already uses.
The §4 "Model B" conjunction is the *blind-application* stance and is needlessly strict here.
The literature's "preserve-bottom" contract is also real, but it is a *different mode* (see below), not a refutation of Model A.

### 8.1 The two soundness modes

There are two distinct, each-internally-sound contracts for replacing a matched `LHS[σ]` with `RHS[σ]`, and they correspond to two different operating assumptions:

- **Blind application — "preserve bottom": `#Ceil(RHS) → #Ceil(LHS)`** (equivalently `LHS = ⊥ ⟹ RHS = ⊥`).
  Sound *without* knowing anything about the redex's definedness: if you might be rewriting a ⊥ redex, the result must also be ⊥ so you never fabricate definedness.
  This is exactly what the **K User Manual requires of `simplification` rules** ("the RHS must be `#Bottom` when the LHS is `#Bottom`, or a `requires`/`ensures` clause must be false when the LHS is `#Bottom`").
  It is a *frontend well-formedness* contract so a rule can be applied by the simplifier wherever it matches, with no σ and no configuration in hand.

- **Assume-defined application — Model A: `#Ceil(LHS) → #Ceil(RHS)`** (equivalently: discharge `#Ceil(RHS)` under the assumptions `#Ceil(LHS) ∧ requires`).
  Sound *given* that the redex is known defined.
  Under that assumption it reduces to "the rule must not introduce new undefinedness in its result" — i.e. each rule must **preserve** definedness.

These two are logically duals, not the same statement, and they genuinely differ for rules whose partial symbol sits in the **LHS** with a total RHS (the KEVM pattern): preserve-bottom *rejects* such a rule, assume-defined *accepts* it.
Note also that "discharge `#Ceil(RHS)` under assumption `#Ceil(LHS)`" is logically identical to "prove `#Ceil(LHS) → #Ceil(RHS)`" — so the literature thread's "correct obligation" and Model A are the same thing; the only substantive literature finding is that K's *blind* contract is the converse.

### 8.2 Why assume-defined is the right mode for Booster (and is sound)

1. **⊥-strictness of application (general, not symbol-specific).**
   In matching logic, symbol application is interpreted pointwise with `∅ • A = A • ∅ = ∅` (Roșu, *Matching Logic Explained*, Def. 2.3–2.4; OOPSLA'16 Def. 3).
   Hence `#Ceil(f(t₁,…,tₙ)) → #Ceil(t₁) ∧ … ∧ #Ceil(tₙ)` for **every** symbol `f` (total or partial).
   So a subterm of a defined term is itself defined: `#Ceil(C[t]) → #Ceil(t)`.
   (The converse, `⋀#Ceil(tᵢ) → #Ceil(f(t̄))`, holds only for total/constructor `f` — that is precisely the §6 "trivially defined" checker.)

2. **Symbolic execution reasons about *defined instances*.**
   A symbolic state `t ∧ P` denotes `{ρ(t) | ρ ⊨ P}`; for valuations where any partial subterm is ⊥, `ρ(t) = ⊥` and that valuation contributes nothing — it is silently excluded (reachability-logic semantics; One-Path/All-Path papers use a total state model with no ⊥-configuration).
   So assuming `#Ceil(config)` — and therefore, by (1), `#Ceil(LHS[σ])` at any configuration subterm — does not lose soundness: the only instances it "ignores" are the vacuous ⊥ ones the claim never quantified over.
   This is the standard meaning of Kore's `assumeDefined` `SideCondition`.

3. **It matches the complete engine, empirically.**
   The KEVM declines are *rescued by Kore*.
   Kore applies `0 <=Int #newAddr(A,B) => true` etc. precisely because it operates in assume-defined mode.
   Matching Kore's behaviour is the goal, so Model A is the target.

4. **The codebase already committed to this — statically.**
   The 2023 ceil work (PR #402, `Booster/Definition/Ceil.hs`) computes the residual as `ceil(RHS) ∖ ceil(LHS) ∖ ceil(requires)` — the set-difference *is* Model A (partial symbols shared by LHS cancel, i.e. `#Ceil(LHS)` is assumed).
   Its commit message states the assumption in the open: *"we … assume (but should eventually check) that the given configuration is defined."*
   So the static analyzer is Model A; only the runtime application gate stayed cruder/conservative (reject any partial symbol it can't statically clear), which is the gap this redesign closes.

Conclusion: read `#Ceil(LHS) → #Ceil(RHS)` as "discharge `#Ceil(RHS)` assuming the redex (and `requires`) — the redex being defined for free from the assume-defined configuration." That is sound for symbolic execution and is what we want.

### 8.3 What this means for the KEVM cases

- `0 <=Int #newAddr(A,B) => true`, `0 <=Int (X <<Int Y) => true`, `#lookup((K1|->V) M, K1) => V` (partial symbol in LHS, total/defined RHS): residual `#Ceil(RHS) ∖ #Ceil(LHS) = #Top`.
  **Apply freely; no runtime discharge needed.**
  The current decline is purely the conservative gate; under Model A these never even produce an obligation.
  In particular the genuinely-partial LHS arithmetic (`X <<Int Y`) needs *no* SMT discharge of `#Ceil(X <<Int Y)` — it is assumed defined as a configuration subterm; the claim's `requires 0 <=Int X` is a *correctness* condition handled by `checkRequires`, orthogonal to definedness.
- `… => 1 /Int X` and other **RHS-introduced** partiality: residual `#Ceil(1 /Int X) = (X =/= 0)` survives the set difference.
  This is the one family that needs a **runtime** discharge of the residual against σ + the path condition (SMT) — the KEVM-team ask in `kevm-doc.md` §5.3, but now scoped to *only* RHS-introduced partiality, not the whole problem.
- "Semantically total but declared `[function]`" symbols (`#newAddr`, `#WordPack*`, `#hashedLocation`, `#bufStrict`): these are an **annotation issue**.
  Marking them `[total]` makes both modes agree (`#Ceil(f(defined args)) = #Top`, and preserve-bottom holds trivially) and is the clean fix the KEVM team already plans.
  Model A buys correctness here without the annotation, but `[total]` is still the right hygiene.

### 8.4 Recommended design (static + dynamic)

**Static (load), per rule:**
- Compute the Model A residual `R = simplify( #Ceil(RHS) ∖ #Ceil(LHS) ∖ #Ceil(requires) )`, reusing/extending the existing `Definition/Ceil.hs` machinery (this already exists for rewrite rules; generalise to the other rule kinds and store the result).
- If `R = ∅`/`#Top`: mark the rule definedness-preserving — applies with no runtime check.
- Else: attach the residual predicate `R` (a conjunction of `#Ceil(partial subterm)` over RHS-introduced partiality) to the rule (a new field on the rule, which does not exist today).
- This replaces the load-time *symbol-name blame list* with a real symbolic obligation, and drops the conservative LHS∪RHS scan: LHS-only partiality must **not** flag the rule (it is discharged by assume-defined).

**Dynamic (apply), only for rules carrying a residual `R`, after a successful match:**
- Substitute σ into `R`.
- Discharge by: (a) structural trivially-defined check (the term has no partial-symbol subterm after simplification — §6, covering reduction to DVs/variables/total terms), then (b) if a symbolic predicate remains, check it against the known constraints / path condition via SMT (the existing `checkRequires` machinery, and the implies endpoint's SMT discharge, are the model).
- Accept → apply the rule; fail → abort *indeterminate* and let the caller (function-eqn / simplification / rewrite / implies) decide (function-eqn priorities are binding → abort; simplification priorities advisory → continue to next rule).

### 8.5 Caveats and guardrails

- **No circular assume-defined.**
  Assume-defined is valid for subterms of the configuration we are simplifying/proving about; it must **not** be used while computing a term's *own* definedness (that would assume what we are trying to decide).
  The nested evaluation used to discharge a residual must run with the definedness assumption **off** — i.e. one level deep, never recursing into another ceil-discharge.
- **Per-site applicability.**
  Assume-defined is justified where the redex is genuinely a subterm of an assumed-defined configuration (execute/simplify of the state, implies under `assumeDefined`).
  It is *less* obviously justified for arbitrary internal evaluations, so the discharge should be controllable per call-site (implies / equation evaluation / simplification / rewrite side conditions) and switched on only where the premise holds; default off / opt-in.
- **Empirical caution (the #440 revert).**
  When the inferred-definedness marking was first enabled (PR #426) it fired a rule that introduced an existential/`?`-variable (`Ex#Var'Ques'STORAGE`) and broke a Kontrol/Optimism proof; it was reverted (#440) and only re-landed (#441) once understood.
  So loosening the gate has a track record of surfacing interactions with existential/question-mark variables — roll out opt-in, and test against Kontrol/KEVM before flipping defaults.
- **`requires` vs definedness are orthogonal.**
  Under assume-defined, LHS-position partiality contributes *no* definedness obligation; the side conditions that look definedness-shaped (`0 <=Int Y` for a shift) are really *correctness* `requires` discharged by `checkRequires`/SMT as today.
  Do not double-count them as definedness residuals.

### 8.6 Correction to §4

§4's "Model A" is the right target; its worked-examples table is correct once read in assume-defined mode (the LHS-partial rows really do reduce to `#Top` and should apply freely).
§4's "Model B" (the unconditional conjunction) is the *blind-application* obligation and is over-strong for symbolic execution — it would force needless `#Ceil(LHS)` discharges that assume-defined gives for free.
The only genuine residual to discharge at runtime is RHS-introduced partiality (`#Ceil(RHS) ∖ #Ceil(LHS) ∖ #Ceil(requires)`), against the path condition.

### 8.7 Source pointers

- K User Manual — `simplification` rules must preserve `#Bottom` (the blind-application contract): kframework.org/docs/user_manual.
- Roșu, *Matching Logic* (LMCS 2017) and *Matching Logic Explained* (JLAMP 2021) — `⌈_⌉` semantics, the `∀x. ⌈x⌉` definedness axiom, total vs partial symbol axioms, the `⌈x/y⌉ = (y ≠ 0)` example; OOPSLA'16 *Semantics-Based Program Verifiers* — set-valued application and `∅`-strictness.
- One-Path (LICS'13) / All-Path (RTA'14) reachability logic — total state model; symbolic states as denotation sets; vacuity of ⊥ instances.
- This repo: `booster/library/Booster/Definition/Ceil.hs` (PR #402, the static Model-A residual via `ceil(RHS) ∖ ceil(LHS) ∖ ceil(requires)`, with the explicit "assume the configuration is defined … should eventually check"); `Internalise.hs:892` (the conservative LHS∪RHS load scan to be replaced); `ApplyEquations.hs:716` (`master`'s binary definedness gate, to be replaced); PRs #426/#440/#441 (the empirical-caution episode); `docs/2020-06-17-Checking-Implication.md` (the in-repo note that checking `⌈t(X)⌉ ∧ P(X)` "could … infer that the configuration is defined, allowing … subsequent rewriting without generating extra definedness conditions" — assume-defined, in our own docs).

## 9. Implementation status on this branch (`ceil-simplifier`)

What has actually been built so far, and the decisions taken (some made autonomously — flag for review).

### 9.1 What is implemented

1. **Residuals attached to rules.** `RewriteRule` gained `definednessResidual :: [Either Predicate Term]` (`Left p` = residual predicate, `Right t` = unresolved `#Ceil(t)`); a rule preserves definedness iff it is empty. `Pattern.Util.collectUndefinedSubterms` mirrors `filterTermSymbols`. Commit: *"gate rule application on a definedness residual"* — a behaviour-preserving switch of the gate from the `notPreservesDefinednessReasons` boolean to the residual.
2. **Uniform static computation.** `Definition/Ceil.computeCeilsDefinition` now walks **all three theories** via a polymorphic `computeRuleResidual` parameterised by a `DefinednessFormula`: rewrite → `Implication` (`#Ceil(rhs) ∖ #Ceil(lhs) ∖ #Ceil(requires)`, unchanged from master), function → `ConjunctionArgs` (`#Ceil(args(lhs)) ∧ #Ceil(rhs)`, head excluded), simplification → `Conjunction` (`#Ceil(lhs) ∧ #Ceil(rhs)`). Commit: *"compute ceil residuals uniformly for all rule kinds, per-kind formula"*. Switching a kind's formula is now a one-line change.
3. **Dynamic discharge.** `ApplyEquations.applyEquation` defers the residual check to after matching and calls `dischargeDefinednessResidual`: substitute the match `σ`, simplify each obligation in an **isolated `runEquationT`** (copied cache/known predicates, fresh iteration state) with discharge disabled, and accept when a `#Ceil(t)` obligation simplifies to a term with no partial sub-terms (the load-time "trivially defined" check) or a predicate simplifies to `true`. Commit: *"dynamic ceil discharge at rule application"* (+ unit tests).

### 9.2 Decisions taken (review these)

- **Dynamic discharge is always on**, not behind a flag. `EquationConfig.dischargeDefinedness` defaults `True` (set in `runEquationT`) and is flipped `False` only for the discharge's own nested simplification, giving a **one-level-deep** guard (no recursive discharge). The earlier per-site `--evaluate-ceils-*` flags were *not* reintroduced; if per-site control is wanted, the flag now exists and just needs threading from `GlobalState`/CLI.
- **Isolation via a fresh `runEquationT`** (not `local`/`withReaderT` over the live state). An in-place nested simplify corrupted the outer traversal's iteration state (`changed`, cache) — caught by the `f2` unit tests, which returned the whole term unevaluated. The isolated run (copying `cache`/`predicates`) fixes it and mirrors the rebased-out prototype.
- **Discharge check = the load-time "trivially defined" test**, per the request: `collectUndefinedSubterms == []` for `#Ceil(t)`, `== TrueBool` for predicates. No SMT / path-condition entailment for residual *predicates* yet — only structural/concrete discharge. (Symbolic conditions like `Y =/= 0` provable only from the path condition still do **not** discharge. That is the obvious next increment if wanted.)
- **`internalise` keeps a cheap raw-scan residual as a fallback**; `computeCeilsDefinition` (run at server load) overwrites it with the real `computeCeil` residual. So a definition loaded *without* the ceil pass is more conservative than one loaded with it, and **the unit tests exercise the fallback** (they do not run `computeCeilsDefinition`), while the per-kind `computeCeil` formulas run at the server.
- **`notPreservesDefinednessReasons` is retained** (not removed) for the abort message and to select which rules `computeCeilRule` refines. Retiring it is a clean follow-up once the residual is the sole source of truth.

### 9.3 Behaviour change vs master, and validation gaps

- Rewrite rules: unchanged (same implication residual as master).
- Function/simplification rules: now more permissive — residuals that discharge **at load** (concrete arithmetic, concrete collection distinctness, explicit `#Ceil` rules) and, with dynamic discharge, residuals that discharge **once the match is known** now let the rule apply. Symbolic partial subterms still reject, so the KEVM LHS-partial declines are **not** expected to move (matching the analysis in §8.3); the genuinely-partial-arithmetic family needs the SMT/path-condition step that is not yet built.
- **Validation:** 982 booster unit tests pass (incl. a positive + negative dynamic-discharge test). The new per-kind `computeCeil` formulas and the always-on dynamic discharge are **not yet exercised against the booster/KEVM integration suite** (needs the K toolchain) — that is the outstanding validation before trusting the behaviour change or flipping anything KEVM-facing.

### 9.4 Commit sequence (on the `#4156` base `163997f9b`)

1. `docs/…definedness-checking-design` — this document.
2. `…: gate rule application on a definedness residual` — residual field + gate switch (behaviour-preserving).
3. `Definition/Ceil: compute ceil residuals uniformly for all rule kinds, per-kind formula`.
4. `Pattern/ApplyEquations: dynamic ceil discharge at rule application`.
5. `unit-tests/ApplyEquations: tests for dynamic ceil discharge`.
