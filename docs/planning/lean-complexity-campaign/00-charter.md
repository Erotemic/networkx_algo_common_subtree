# 00. Charter and design decisions

## 1. Problem to solve

For a new dynamic program, a client should describe its state space, recursive requests, local work, data representations, and any reuse between subproblems. The reusable library should discharge the consequences of that description: how often a state is expanded, how often a lookup occurs, how costs compose, how stored potential can be spent, how a concrete operation implements an abstract one, and how an explicit bound becomes a multivariate asymptotic specification.

The client must still prove its actual mathematics: state-space closure, correctness of its recurrence, the validity of a schedule, and the combinatorial reason a collection of matching repairs is cheap. A generic library cannot infer the Droschinsky speedup solely from the words "warm start" or "memoization."

The objective is to remove repeated semantic and bookkeeping proofs **without hiding the mathematical premises that make a bound true**. The output must be useful outside tree matching. Candidate independent consumers include edit distance, reachability over a DAG, a sequential amortized queue, and a batched reoptimization algorithm.

## 2. What justifies substantial investment

There are three different kinds of work. Keep their evidence and claims separate.

| Kind | Example | Standard for accepting the work |
|---|---|---|
| Reusable mathematical theorem | Weighted work charging; a finite dependency evaluation bound | Precise statement, correct premises, citations or explicit original synthesis, independent applications |
| Reusable semantic theorem | Operational adequacy; cost-refinement composition; credit conservation | Actual semantic definitions, nonvacuous soundness, checked proof, meaningful source instance |
| Proof engineering | Adapter, tactic, `simp` API, counter extraction | Measurable client benefit, kernel-generated proofs, no new trusted inference |

The elementary telescoping inequality is worth reusing but does not, by itself, justify a major foundational project. The substantial contribution would be an implementation-linked theorem with a reusable statement and a practical proof interface. Conversely, an engineering adapter need not masquerade as a difficult new mathematical result to be valuable.

A candidate for a Tau Ceti roadmap must pass the user's stronger test: substantial proof content, precise provenance, and independent reuse. If it is a proposed synthesis rather than a theorem stated in a paper, say so and identify the individual published ingredients. Do not manufacture a theorem number or call a new interface a classical theorem.

## 3. Fixed decisions

**D01. Preserve independent specifications.** Existing tree, embedding, matching and optimum definitions remain the source of semantic meaning. Cython is historical evidence, not a correctness oracle. Generated Rust-to-Lean code remains generated.

**D02. Preserve the current baseline during reconnaissance.** No global Lean, Mathlib, Aeneas or Cargo upgrade is part of this overlay. Experiments may use separate worktrees or standalone Lake packages. Any eventual dependency change gets an explicit compatibility and migration report.

**D03. Reuse existing mathematics.** Prefer Mathlib finite sums, orders, filters, asymptotics, well-founded relations and graph infrastructure. Do not introduce a parallel definition of big-O merely for convenient syntax. Packaging a clearer specification over `Asymptotics.IsBigO` is acceptable.

**D04. Reuse an execution and proof backend when possible.** arlib, Lax62, `Std.WP`/`vcgen`, and Iris-Lean have different roles. Test them instead of deciding from a name, a README, or a constructor being private. A hybrid adapter is allowed, but multiple semantic models must have an explicit connecting theorem.

**D05. Choose deterministic sequential work as the first resource.** Use natural-number work, with operation descriptors or vectors when useful. Peak memory, expected cost, parallel span and bit complexity have separate semantics. No universal resource hierarchy is required before the first client.

**D06. Source cost enters early.** The first actual lookup and loop must expose how recorded work is connected to executed work. A handwritten "charged twin" with value equality alone does not close that obligation.

**D07. Charge representation work.** Equality on a pair of Dyck words is not automatically one RAM instruction. Slicing, hashing, cloning, allocations, arithmetic precision, output witnesses and adapter conversions must either be counted or explicitly excluded by the chosen claim.

**D08. Separate uniform worst-case, amortized and expected bounds.** A constant-time abstract dictionary contract is not a theorem about randomized hashing. A per-operation amortized contract includes state and potential. A result about one fixed word width is not automatically an asymptotic theorem over arbitrarily large inputs.

**D09. Generalize from consumers.** One local program plus one structurally independent client is the minimum evidence for stabilizing a generic interface. Do not make every field universe-polymorphic, algebraically generic or effect-polymorphic before a consumer needs it.

**D10. Keep the package extractable.** General modules must not import `SubtreeProofs.Paper2004`, `Droschinsky2016`, `Droschinsky2018`, generated Rust, or tree-specific scoring. Local adapters import the generic package, never the reverse.

## 4. Decisions deliberately unresolved

* Whether arlib's charged model plus its realization relation is the primary backend, or whether the timed-refinement stack provides a better semantic spine.
* Whether an execution trace is explicit proof data, an inductive relation, or derived from a backend evaluator. The public client contracts should not depend on storing traces at runtime.
* Whether the source-cost pilot is based on a small instrumented Rust/LLBC semantics, a supported extraction transformation, or a reviewed compositional interpretation of the generated function's control flow. Each route needs a precise trust statement.
* Whether ownership needed for matching-family reuse is expressible with a linear batch ledger, or requires a separation logic. Do not choose the larger framework without the batch counterexample and pilot.
* The eventual upstream home. Tau Ceti quality is the planning standard. Mathlib, CSLib, arlib, Iris-Lean, an Aeneas extension, or a small independent package may be better homes for different pieces.

These decisions have experiments in [09](09-execution-plan.md). They are not vague future tasks: each has evidence requirements and a concrete outcome that changes the next work package.

## 5. Claim ladder

Every exported result must label its level:

| Level | What is established | What is not implied |
|---|---|---|
| C0: mathematical work | Bound on an independently defined event family or recurrence | That source code generates those events |
| C1: instrumented evaluator | Bound on cost produced by a specified evaluator | Cost of arbitrary functionally equivalent code |
| C2: operational adequacy | Bound on steps/events of a specified operational semantics | Compiler or hardware cost preservation |
| C3: source correspondence | C2 connected to pinned source and primitive models | Exact CPU cycles, allocator behavior, extraction of unsupported features |
| C4: compiled-machine correspondence | Cost bound in an explicit machine semantics | Wall-clock bounds on an unspecified machine |

Amortized, probabilistic and space qualifiers are orthogonal to these levels. A C1 expected bound is still C1. Do not upgrade a level through a benchmark, an instrumented trace sample, or a matching result type.

## 6. Campaign success criteria

A successful first campaign produces a reusable memoized evaluation theorem, cost-aware composition rules, a real source-level pilot, and at least two independent clients. A successful extension proves a general batch-accounting contract and instantiates it for one of the matching-family algorithms. A successful upstream contribution is the smallest coherent subset of those results that can be documented, built, reviewed and maintained independently.

Record proof burden before and after: which old lemmas are replaced, which algorithm-specific invariants remain, how many independent semantic adapters are required, which constants are hidden in client specifications, and whether a new client requires changes to the core. Do not use lines of code or a count of lemmas as the sole success metric.

The campaign should be redirected if an inspected upstream package already provides the missing theorem with a suitable interface. Adapting and applying it is a successful outcome. The goal is easier trustworthy complexity proofs, not ownership of another framework.

## Sources

Research basis: [L01--L09], [R01--R10], [I01--I05], [A01--A04] in [14-bibliography.md](14-bibliography.md). All proposed architecture and gates in this document are campaign design decisions, not statements attributed to those authors.
