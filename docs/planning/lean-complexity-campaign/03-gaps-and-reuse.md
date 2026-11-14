# 03. Gap analysis and reuse decisions

## 1. What "missing" means here

Use four statuses: **available**, **adapter needed**, **candidate general theorem**, and **algorithm-specific obligation**. Reserve "absent" for a named declaration or capability searched in a pinned codebase, with the search scope recorded. This audit does not prove that no Lean library contains a generic memoization cost theorem.

The most consequential gaps are often between existing components: a good cost algebra may lack the adapter to our evaluator, and a good runtime proof may expose constants in a form that makes every client brittle. Those are worthwhile gaps even when all underlying mathematics is known.

## 2. Gap ledger

| ID | Need | Evidence/status | Required next action | Do not do |
|---|---|---|---|---|
| G01 | Multivariate big-O and algebra | Available in Mathlib [L01] | Compile wrappers at the project pin; specify admissible filters | Reimplement Landau notation |
| G02 | Operation currencies and pricing | Available candidates [L02, L05, I03] | Inspect exact rates, state dependence, and exchange laws | Assume a dictionary lookup is one machine step |
| G03 | Compositional execution-cost adequacy | Existing model-specific endpoints [L02, L05, L14]; source adapter missing locally | Compare realized programs and counterexamples | Treat `pure expensiveFunction` as source cost zero |
| G04 | Verification-condition generation | Existing `Std.WP`/`vcgen` [L04] | Cost-aware WP pilot with a local loop | Commission a new tactic language first |
| G05 | General memoized evaluation/counts | Local specialized proof and Lean correctness examples [L16] exist; exact generic resource endpoint not identified | Search candidate packages, then generalize with multi-root warm-cache client | Repeat call/miss proofs per algorithm |
| G06 | Dynamic request multiplicity and representation costs | Local counters cover only a subset | Event occurrences plus concrete lookup/key contracts | Replace a request list by a set of edges |
| G07 | Schedule correctness and work | Paper-specific schedules remain; generic DAG layer is a candidate | Separate readiness proof from schedule construction and execution costs | Assume an arbitrary order is topological |
| G08 | Modular amortized specifications | Classical theory and implementations exist [R01--R05, I05] | Bind potentials to actual persistent state/ownership | Present telescoping alone as the hard contribution |
| G09 | Batched shared initialization and repairs | Candidate generic accounting interface; matching invariant still local | Prove ledger conservation and bounded event fibers | Claim reuse always reduces complexity |
| G10 | Persistent branching credits | Established hard work in Rocq [R05]; Lean exact coverage not audited | Test clone/fork counterexample and ownership backend | Spend the same potential once per clone |
| G11 | Data-structure implementation costs | arlib contracts and RAM examples exist [L02] | List-backed/direct-address pilot; audit array/copy primitives | Import an opaque optimized map as verified constant-time |
| G12 | Rust-to-resource correspondence | Not established by local functional theorem | Small instrumented source semantics/translation bridge | Infer runtime from output equivalence |
| G13 | Readable asymptotic subroutine specs | CFML precedent; Mathlib substrate | Opaque dominating cost envelope plus exact execution spec | Carry implementation constants through every caller |
| G14 | DP live space and wrappers | Local target remains; source models abstract allocation/stack | Live-value schedule and representation residency contracts | Equate table cardinality with total process memory |
| G15 | Expected hash costs | Separate probabilistic foundations [R06--R07] | Explicit randomness, key cost, adversary and history conditions | Rename a worst-case assumption "expected hashing" |
| G16 | Parallel time/span | Dedicated 2026 precedent [R09] | Separate later work/span semantics | Use additive work as elapsed parallel time |
| G17 | Weighted matching optimized family | Existing correctness; paper-specific costs open | Instantiate generic accounting with a real repair/schedule proof | Reprove general assignment duality unnecessarily |

## 3. Recommended ownership of work

### General mathematics

Finite weighted charging, finite state/dependency bounds, potential inequalities, schedule/frontier results and parameter-uniform asymptotics should use ordinary Lean mathematical objects. They should be independent of arlib, Aeneas and a specific logic whenever the statement permits. This is the likely upstream mathematical slice.

The intrinsic proof of some ingredients is short. The contribution test belongs to the coherent reusable theory and its hard soundness results, not to the length of every lemma. Do not inflate a simple fiber-counting lemma into a research milestone.

### Semantic adapters and program specifications

Operational adequacy, cost-aware refinement, memo interpreters and program specifications belong close to their backend. If arlib already proves the required realization theorem, write the adapter and use it. If Lax62 already proves the required timed-refinement theorem, identify the real assumptions and add the DP client. If `Std.WP` is sufficient for a small program model, register sound specifications and reuse `vcgen`.

A project-neutral interface should expose the relation between input, output, state and resource bound. It should not erase which semantics was used. Avoid a universal `VerifiedCost` badge whose only content is an arbitrary proposition supplied by the caller.

### Local algorithm layer

State closure for LV2004, degree-sensitive matching-family bounds, signed-weight reductions, oriented-tree recurrence decomposition, two-pass schedule readiness, and wrapper correspondence remain local until their independent reuse is demonstrated. They are important outputs, but need not all become general library abstractions.

## 4. Backend comparison rubric

For each candidate, fill the same evidence table. A yes/no README answer is insufficient.

| Question | Required evidence |
|---|---|
| What is executed? | Definition of evaluator/small-step semantics and successful/error outcomes |
| What is counted? | Event or primitive definition; branch, loop, allocation and call conventions |
| Why is it adequate? | Exact theorem signature connecting cost to execution, with premises expanded |
| What can be free? | Audit of `pure`, callbacks, specification views, indexing and logical computation |
| Is correctness independent? | A client theorem against a specification not defined as the evaluator itself |
| Does it compose? | Checked sequential/branch/loop/subroutine application on the same pilot |
| How are failures handled? | No vacuous empty-result or top specification; successful and error path policy |
| What does source refinement mean? | Pin and relation to existing code, or an explicitly narrower C1/C2 endpoint |
| What is the maintenance cost? | Toolchain/import/license compatibility and proof size of adapters |
| Does it help a second client? | Unrelated DP or graph algorithm using the unchanged public interface |

The winner need not maximize features. Prefer the smallest backend that closes the required proof boundary and supports the clients without opaque assumptions. Do not give a fixed numerical score before the experiments; some failures, such as an unproved adequacy assumption, are categorical for a C2/C3 claim.

## 5. Reuse decisions already justified

Use Mathlib asymptotics. Keep the existing independent matching and tree specifications. Retain Aeneas as the current functional source boundary. Do not add the whole moving Tau Ceti dependency to get an elementary sum or Dyck-count lemma. Do not treat current CLRS-Lean existence/correctness as the optimized matching runtime theorem. Do not write a new VCG without testing Lean 4.35's one.

No final decision between arlib and Lax62 is justified yet. arlib has a compatible pin and a narrower operation/realization design; Lax62 has a more extensive source-to-machine stack but a different toolchain epoch and additional statement-audit work. Both are serious experimental candidates. An adapter between selected parts is a possible outcome, not a requirement.
