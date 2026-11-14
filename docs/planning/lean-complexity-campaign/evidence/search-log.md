# Research coverage and refresh log

**Cutoff:** 2026-11-14. **Purpose:** identify reusable foundations and recent overlapping work before starting the campaign. **Claim:** a broad, evidence-graded census; not an exhaustive enumeration of private, unpublished or unindexed results.

## Search and inspection routes

The attached source archive was the repository basis. Conversation-file semantic search returned no indexed content for this archive, so the mounted archive and its exact extracted files were inspected directly. The Git baseline, archive hash, manifests, proof crosswalk, library audit, key Lean declarations and actual Rust lookup/evaluator were examined. No separate remote branch was substituted for the upload.

Public research used primary author/publisher pages, official Lean/Mathlib/CSLib/AFP documentation, arXiv versions, public project sources and GitHub connector reads. Secondary search results served as discovery leads and were not used to establish technical theorem claims. Detailed grades and locators are in `sources.json` and `../14-bibliography.md`.

## Coverage families

| Search family | Sources incorporated | Remaining audit |
|---|---|---|
| Lean cost models and asymptotics | Mathlib, arlib, CSLib TimeM, Lean4CStheory, Lax Word RAM/refinement | Exact pinned imports, semantic predicates and builds |
| Lean proof automation and ownership | Lean 4.35 Std.WP/vcgen, Iris-Lean September 2026 | Cost interpretation and precise port coverage |
| Lean algorithms and source verification | Aeneas/local generated proofs, CLRS-Lean, October 2026 order maintenance, memo Sigma-type example | Actual source-to-cost bridge and independent clients |
| Rocq implementation complexity | CFML, union-find, incremental cycle detection, time credits/receipts | Exact statement/artifact inspection for selected ports |
| Rocq shared/probabilistic/parallel/space | Thunks and Debits, Tachis, ExpIris, Memorist 2026, Parcas 2026, heap-space work | Separate semantics; no assumed Lean port |
| Extraction, compilation and complexity models | Certifying extraction, reasonable lambda cost models, Cook-Levin, CertiRocq, CPP 2026 RISC-V bounds | Strength and scope of cost preservation |
| Isabelle | Memoization/DP, NREST/AFP, timed refinement, LLVM time, amortized analysis | Existing Lean-port overlap; artifact compatibility |
| Alternative type/analysis methods | Calf, decalf, AARA/RaML, Atkey, Danielsson | Selected original theorem details; inference is not a first-stage requirement |
| Recent adjacent campaigns | AutoCLRS/AlgoStar and specification audits; verified optimization October 2026 | Do not equate ghost counters, measured speedups or value equivalence with source cost |
| Target algorithms | Uploaded LV/DKM crosswalk and proofs; original DKM2018 HTML | Exact local matcher and schedule resource proofs |

## Explicit final recency pass

The final pass used search queries including:

```text
Lean algorithm complexity resource verification cost semantics 2026 memoization time credits
Rocq Coq cost analysis complexity 2026 CertiCoq time space verification
AutoCLRS 2026 Microsoft Pulse complexity verified algorithms
Lean FAD dynamic programming algorithm design Haskell Lean verified
Forster Kunze certifying extraction time bounds Coq 2019
Gaher Kunze 2021 Cook Levin Coq mechanised
Forster Kunze Roth 2020 time space complexity weak call by value lambda calculus
```

The first two were freshness-filtered to the preceding 180/365 days respectively. They surfaced the October 28 order-maintenance preprint and the current CertiRocq project. Following primary sources added L14--L17, R13--R16 and A08. Publication dates were taken from primary records, not search-engine crawl dates. Old papers with recently regenerated PDFs were kept at their actual publication dates.

The FAD project surfaced as an additional correctness/refinement lead through secondary listings. Its source was not audited here and it is not counted as a verified runtime backend. A final pre-implementation refresh should inspect it when choosing independent DP examples. Similarly, a claim on an unrelated project page that Lean has no cost model was not accepted as absence evidence.

## Concrete inspected source anchors

* arlib `8d08f89a6d05c5e8368e91659bd6e117fbb74c4e`: selected cost/charged material and `ExactRealization.lean`, including `ExactRealizes`, `bind`, `steps_eq` and primitive examples.
* Lax62 `0503df0eaf4e41104b9a3aa31e3e028b5adf7a0e`: registry, source tree, root imports, NREST `Basic.lean` and `Codegen/Examples/EndToEnd.lean` opening sections. This is selected-source inspection, not a complete theorem/axiom audit.
* Lean 4.35 release/reference and `vcgen` documentation; live API documentation may be newer than the project's exact Mathlib pin.
* Order-maintenance paper HTML and repository README blob `5a98944785cb2b4f6781ba0a8251252926d6d4fc`; theorem files named in the README were not built or fully audited here.
* `complexity-lean` README blob `cd063842829eaaa17adc3ff217299eaa7fd9bae8`; its model-specific and explicitly conditional claims were retained.

## Retrieval and verification limits

Some paper PDFs could be parsed or visually inspected, including selected timed-refinement and thunks/debits pages. Some PDF retrieval/rendering attempts failed; author/publisher/HTML records were used where available. The bibliography records a failed memoization PDF fetch and a failed LLVM-time screenshot retrieval rather than implying full visual inspection. No source screenshots or papers are packaged in this text-only overlay.

Container network cloning was unavailable. Web/GitHub reads supplied selected upstream source, and the already mounted archive supplied local code. No Lean/Lake executable was available, so no external package or proposed signature was compiled. Existing repository test reports were read as historical reports, not rerun. No maintainers were contacted and open PRs/Zulip threads were not exhaustively traversed.

## Refresh procedure before committing major effort

Re-run recent searches at G0 and before submission; check the exact selected projects' releases, issues and pending proposals; follow new papers' formal-artifact links; compare theorem definitions and hypotheses at pinned revisions; inspect selected APIs for unproved assumptions; and build an independent consumer. Add a census record with the evidence grade even when the result remains a lead. Narrow a negative claim to the actual search scope.

Do not spend indefinitely refreshing every adjacent topic. The decision-relevant stopping point is a declared semantics and a same-task pilot that can distinguish reuse from a real missing adapter/theorem. Unresolved adjacent leads remain visible research debt rather than a claim of comprehensive absence.
