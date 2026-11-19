# 10. Validation and review

## 1. What validation must establish

There are independent review questions: Is the mathematical statement true? Does Lean prove that statement? Does it describe the intended algorithm? Does the resource model cover the executed work? Does the result compose into the claimed end theorem? A build checks only part of this chain.

For each completed target, review the full declaration type, definitions of its premises, imported assumptions and the consumer theorem. A result with a premise equivalent to the desired complexity conclusion may be logically valid but contributes no reusable proof.

## 2. Statement and provenance review

Record exact publication/revision, theorem or section, conventions, and the difference between the source statement and the formal one. Classify the formal result as faithful instance, stronger generalization, corrected statement, equivalent reformulation or original synthesis. Do not use a broad paper citation to imply that a proposed interface appears there verbatim.

Inspect nearby false statements. Important cases include duplicated requests treated as sets, baseline potential spent once per branch, free structural comparisons, vacuous successful-run bounds, fixed-width inputs treated as an infinite asymptotic domain, and a costly wrapper attached to a cheap core theorem.

For the local papers, preserve the LV containment correction and the DKM signed/partial/nonempty distinctions. Check that `cost` means runtime rather than assignment objective weight before admitting a declaration to the complexity census.

## 3. Kernel and trust review

Production theorems must not use `sorry`, `admit` or a new unsupported axiom. Print axioms for final interfaces and representative consumers. Standard Lean logical principles such as propositional extensionality, choice and quotient soundness are not automatically errors; record them under the project's accepted foundation. Review any additional axiom or external oracle separately.

Axioms introduced by an operational semantics are assumptions of the result, not evidence that the source obeys that semantics. A primitive resource specification needs an implementation proof or a prominently stated trusted model assumption. No hidden constant-time assumption for an arbitrary callback is acceptable.

Tactics should construct kernel-checkable proofs. Any use of native evaluation or a special trusted evaluation path must follow the repository's explicit trust policy. Do not equate successful evaluation of finitely many samples with a universal equality theorem.

A standalone upstream `Suggested.lean` may use `sorry` only as a declared roadmap statement artifact under the upstream format. It is not a completed theorem and must not be imported into production proofs. This overlay contains no such checked artifact; creating and compiling it is a later gate.

## 4. Semantic validation matrix

| Test or review | Failure it is intended to expose |
|---|---|
| Program returns the right value after an extra scan | Functional refinement used as cost refinement |
| One diverging nondeterministic branch | Existence of a successful run mistaken for total correctness |
| Empty or inconsistent precondition | Vacuous source/algorithm theorem |
| Repeated request to the same dependency | Set cardinality substituted for occurrence count |
| Two roots share a descendant | Repeated expansion or double-paid preparation |
| Warm cache with a changed input environment | Unsound memo key/context invariant |
| Cache eviction or invalidation | Once-per-key theorem applied outside its hypotheses |
| Lookup at first/last/missing key | Incorrect scan-length or early-exit accounting |
| Long structurally equal keys | Equality hidden inside a constant-cost primitive |
| Full table allocation with few reached states | Initialization omitted from a sparse bound |
| Forked persistent state | Initial potential duplicated across branches |
| Full clone/reset per matching job | Shared-work saving absent from the source |
| Zero dimensions and singleton trees | Logarithm, empty-sum or leading-term assumptions |
| Highly unequal tree sizes/degrees | Nonuniform asymptotic constants |
| Early retirement followed by a read | Logical live-set bound detached from the schedule |
| New output before freeing old input | Peak space confused with end-of-step residency |
| Large witness/output representation | Score-only cost incorrectly attached to an output API |
| Algorithm branch always selects the slower matcher | Existence of a fast algorithm substituted for actual dispatch |

These are semantic examples or targeted proof/client tests. They are not instructions to add source-text guard tests, tests of theorem counts, or permanent migration checks. Prefer actual executable behavior, specification counterexamples and theorem applications. Keep intentionally false declarations outside ordinary production imports.

## 5. Resource accounting audit

For an execution, create an operation inventory partitioned into initialization, control flow, local body, recursive/dependency requests, primitive implementations, storage, output and finalization. Each performed operation must be charged in some category, or explicitly excluded by the model. Double charging can be safe for an upper bound, but should be identified; omitted work cannot be excused by a generous-looking big-O result.

If event traces are proof artifacts, they need not be stored by the runtime implementation. The adequacy theorem must still relate them to execution. Sampling traces is a useful debugging tool, never a replacement for that theorem.

For state-dependent primitive costs, audit the pre-state and operand-size envelope at the actual occurrence. For potential contracts, check that incoming credits are owned, outgoing credits are preserved and no branch spends them twice. For bounded-fiber accounting, inspect the charge map and multiplicity bound rather than only the final finite-sum inequality.

For abstract storage profiles, distinguish retained inputs, temporary scratch, outputs and allocator-independent occupancy. For source memory claims, add the representation and lifetime argument. Do not infer bit complexity from arithmetic-operation counts.

## 6. Integration checks

The following commands are taken from or aligned with the repository's maintained verification workflow. They are **future implementation checks**, not claims that this documentation run executed them. Reopen `proofs/VERIFICATION.md` before running them on a changed baseline.

```bash
(cd proofs && lake exe cache get && lake build)
dev/regenerate_rust_lean.sh --check
cargo test --locked --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
cargo test --locked --manifest-path rust/crates/verified_assignment_core/Cargo.toml
(cd proofs && lake env lean Tests/RootedDynamicProgram.lean)
python -m pytest tests
```

Add exact new module/consumer commands after files exist. Do not publish a nonexistent test target as a verified command. New upstream dependencies are first built in isolated packages with their own pinned manifests. A compatibility migration must preserve existing independent correctness statements and record all changed dependency versions.

Generated Lean must reproduce from source; never repair it by hand. A changed source or translator pin invalidates a source-hash-based realization claim until the generation/correspondence check is rerun.

## 7. API and proof-experience review

A reviewer should implement one small new client using only public contracts and documentation. Record every required internal unfolding or manually repeated accounting induction. This is stronger evidence of usability than a demonstration authored by the interface designer alone.

Compare exact and abstract specifications. Hidden constants should be hidden behind a proved envelope, not omitted. Check that the asymptotic filter is nontrivial and matches the full intended input family. In particular, a product `atTop` limit in two variables does not automatically cover one variable held fixed; use a uniform pointwise envelope or an appropriate domain/filter.

Assess import cycles, elaboration costs and dependency size after correctness. Do not optimize proof-script brevity by weakening the theorem or adding a universal resource assumption.

## 8. Completion evidence and reporting

A completed target has a declaration, checked proof, semantic/provenance record, independent consumer, negative example and source/model boundary. Its machine-readable status should distinguish `statement_checked`, `proved_in_build`, `consumer_integrated`, and `source_connected` rather than collapse them into `done`.

Documentation checks for this overlay are recorded separately in [evidence/validation-report.md](evidence/validation-report.md). They include path safety, link/ID integrity, dependency acyclicity, baseline hashes and package integrity. They do not establish the validity of proposed Lean signatures or any new complexity theorem.
