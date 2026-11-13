# Droschinsky-Kriege-Mutzel (2016, 2018): verified Rust and Lean program

Status: planning and source audit; no accepted Lean proof or Aeneas verification yet.
Audit baseline: `networkx_algo_common_subtree`, supplied snapshot `af0bbdb` (2026-11-13).
Relation to the Lozano-Valiente roadmap: parallel, separate formalization of **unordered, weighted trees**. Share only proven generic infrastructure such as finite trees and maximum-weight matching, never silently identify the ordered edge-contraction problem with topological embeddings.

## 1. Target results

Build two separately stated and verified results, both connected to code generated from the *actual* Rust implementation via Charon/Aeneas:

1. **2016: maximum common subtree isomorphism (MCSI)** between unordered, unrooted, vertex/edge-weighted trees. Prove validity and maximum weight of returned node correspondence. Support the paper's allowed weight semantics and prove a meaningful bound for the implemented algorithm. Prove the paper's faster asymptotic bound only for an implementation that actually incorporates its faster matching/subproblem techniques.
2. **2018: largest-weight common subtree embedding with distance penalties (LaWeCSE)**. Formalize the rooted topological-embedding definition, rooted/unrooted cases, path-based scoring, skipped-vertex penalties, recurrence and witness optimality. Prove cost bounds only when justified by actual matching and DP implementations.

A clean independent mathematical contract is a prerequisite. Agreement between Rust and the current Python oracle does not establish correspondence to the papers.

## 2. Authoritative publications and related work

The public papers are sufficient to begin specification and correctness proofs. Their implementations of the *best complexity bounds*, however, rely on more specialized matching/subproblem arguments requiring a separate line-by-line study.

| Role | Source | Link | Needed for |
| --- | --- | --- | --- |
| Primary 2016 | Andre Droschinsky, Nils M. Kriege, Petra Mutzel, *Faster Algorithms for the Maximum Common Subtree Isomorphism Problem*, MFCS 2016, DOI `10.4230/LIPIcs.MFCS.2016.33` | https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2016.33 ; https://arxiv.org/abs/1602.07210 | MCSI definition, rooted/unrooted DP, matching reuse, asymptotic and enumeration results |
| Primary 2018 | Same authors, *Largest Weight Common Subtree Embeddings with Distance Penalties*, MFCS 2018, DOI `10.4230/LIPIcs.MFCS.2018.54` | https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2018.54 ; https://arxiv.org/abs/1805.00821 | Topological embedding, path weights, skip-penalty semantics, two-state recurrence, complexity |
| Foundational related work | Gupta and Nishimura, largest common embeddable subtree | Cited in 2018, Sections 1 and 3 | Distinguish topological embedding from edge contraction; unweighted recurrence |
| Matching improvements | Ramshaw and Tarjan, unbalanced weighted matching; other matching references cited in 2018 | Follow 2018 Lemmas 7-8 and bibliography | Necessary for claimed near-optimal running time |
| Enumeration extension | Droschinsky, Heinemann, Kriege, Mutzel, *Enumeration of Maximum Common Subtree Isomorphisms with Polynomial-Delay* (2014) | https://eprints.cs.univie.ac.at/6745/ | Optional later verification of enumeration of all optima |
| Different problem | Lozano and Valiente (2004), ordered common embedded subtree | See `docs/planning/lozano_valiente_2004_verified_rust_lean.md` | Disambiguation: edge contraction, ordered structure, different optimization problem |

**Reference acquisition actions:** Pin bibliographic metadata, full versions and any mathematical errata/appendices in a short source ledger; record the exact definition/lemma/equation/page for every formal claim. Prefer linking to papers and versioned sources rather than committing PDF binaries. Inspect full arXiv versions alongside conference papers before locking theorem statements.

`dev/notes/notes.txt` says an author responded with reference implementations on 2025-03-12 and that publicly shareable portions were ported to Rust on 2026-05-12. These original reference implementations are **not present** in the supplied tree. Treat that note as provenance, not as permission to redistribute source or as a replacement for the published specification. Recover and inspect any originals only if appropriate and authorized; they are not a formalization dependency.

## 3. Existing repository inventory

| Path | Current role | Disposition |
| --- | --- | --- |
| `dev/notes/notes.txt` | Original research notes, paper links, author-contact provenance | Preserve, supplement bibliographic record |
| `dev/common_subtree_algorithms_notes.md` | Design intent, implementation status, future validation | Preserve, update when contracts are fixed |
| `docs/source/common_subtree_algorithm_families.rst` | Critical ordered/unordered distinction | Keep consistent with proof contracts |
| `docs/source/common_subtree_correctness.rst` | Informal definitions and recurrence proof sketch | Turn into paper-to-theorem ledger, correct mismatches |
| `docs/source/common_subtree_algorithms_rust.rst` | User-facing crate description | Update after correctness gates |
| `rust/crates/common_subtree_algorithms/src/tree.rs` | Working MCSI DP; experimental LaWeCSE prototype | Preserve as baseline; refactor verification core separately |
| `rust/crates/common_subtree_algorithms/src/matching.rs` | Dense Hungarian solver with optional unmatched vertices | Useful baseline; prove or replace with verified primitive |
| `networkx_algo_common_subtree/common_subtree_reference.py` | Independent *enumeration strategy* but partially shared scoring semantics | Correct paper objective before accepting as oracle |
| `rust/crates/common_subtree_algorithms/tests/` | Matching, isomorphism, embedding, witness tests | Add paper-specific and exhaustive differential cases |
| `tests/fixtures/common_subtree_cases.json` | Named reproducible cases | Add independent paper examples and counterexamples |
| `rust/crates/common_subtree_algorithms/benches/` | ResNet-shaped comparison trees | Retain as performance characterization; never conflate with correctness proof |

No Lean formalization of either Droschinsky result and no translated Rust-to-Lean proof are present in this baseline. The Droschinsky branch already contains the graph-algorithm crate and notes; older C/Cython/packaging branches do not appear to add a separate Droschinsky mathematical source development.

## 4. Confirmed mismatch: 2018 paper scoring versus the repository

**Paper authority:** MFCS 2018 Definition 4 (pages 54:5-54:6), Lemma 5 (page 54:6). When a topological path from a mapped common edge has length greater than one in **either** input tree, the edge contribution is **only** `-p * (len_left + len_right - 2)`. An edge-label similarity weight is credited **only** if both corresponding paths have length one.

Current `networkx_algo_common_subtree/common_subtree_reference.py`, `_score_embedding_bijection`, lines approximately 488-496, instead scores the first edge of each path and adds that weight *even when either path has skipped vertices*. This can both overstate scores and incorrectly reject legal embeddings when those first-edge labels differ. The Rust `compute_rooted_embedding_with_roots_mapped` uses first-step `scoring.edge_weight` in its matching transition, so the underlying contract is similarly restricted. The existing witness-rescoring tests reproduce the repository convention; those tests do not validate the paper convention.

**Regression witness A:** left tree: two mapped endpoints with vertex labels `[1,2]` connected by edge label `5`; right tree: `[1,9,2]` in a path of length two, both edges label `9`; unit matching-node score, skip penalty `0.25`. Paper permits both endpoints to be mapped and gives score `1 + 1 - 0.25 = 1.75`. Existing Python reference returns `1.0` and one node because edge labels mismatch.

**Regression witness B:** same inputs, except both edges on right have label `5`. Paper still gives `1.75`; existing Python reference returns `2.75` by adding an edge reward despite the skipped vertex.

Do not patch tests to match current code. First make an independent paper-scoring evaluator. Replace the reference oracle's scoring with the paper definition, add both fixtures, and use the resulting failures to guide Rust repairs. If the current scoring behavior is wanted as an extension, give it an explicit independent objective and API rather than presenting it as the 2018 theorem.

## 5. Independent mathematical specifications

### 5.1 Shared finite-graph and scoring layer

- Define finite simple undirected trees with connectedness and acyclicity, label maps, adjacency, unique paths, root/parent/child orientation and path interior.
- Define valid partial bijections, finite nonempty or explicitly empty solutions, weight sums, validity of witnesses, maximum scores and existence of optima.
- Use exact mathematical integer/rational scores initially, plus explicit forbidden compatibility; distinguish the formal mathematical weights from the production Rust `f64`, `EPS = 1e-9`, and sentinel `-1e100`. Decide how zero, negative, forbidden, infinity, NaN and ties are specified. Provide exact scoring implementations early.
- Define finite weighted bipartite matching with forbidden pairs and optional unmatched vertices, and prove optimality of the matching specification independently of Hungarian code.

### 5.2 MCSI (2016)

- Common subtree = connected subgraphs selected from both trees; witness = adjacency-preserving bijection with compatible mapped vertex and edge pairs.
- State the objective as the sum of mapped vertex-pair and edge-pair weights. Fix empty-match policy and root restrictions explicitly, including negative weights.
- Prove rooted branch independence, matching reduction, witness assembly feasibility, optimality of each rooted DP state, and completeness of the unrooted maximum over valid root choices.
- Then prove the reduced-subproblem and related-matching properties used by the **faster** 2016 algorithm. The present full-root-pair DP with a dense padded Hungarian matching is a valuable correctness baseline but must not be described as having proved the paper's `O(n^2 Delta)` performance.
- Treat polynomial-delay enumeration of all optimum witnesses as a distinct optional result with separate code and proof obligations.

### 5.3 LaWeCSE (2018)

- Independent topological embedding: injective mappings, descendant preservation in rooted trees, and disjoint interiors of paths leaving different children (paper Definition 1); account for unrooted variants through explicit root/structural choices.
- Common embedding = compatible pair of embeddings of an abstract common tree; show equivalence to the selected-node/bijection representation used by the implementation, *including branch-disjointness*. Do not define correctness merely as equality of a skeleton made from selected vertices.
- Define path contribution **piecewise** as in paper Definition 4: edge-pair similarity if each path length is one; otherwise skipped-interior penalty only.
- Prove the paper's two-state root-mapped versus skipped-root recurrence (Lemma 5), including the exclusivity of edge weight and skip penalty. Reconstruct a witness with explicit paths, not solely a node-pair list.
- Prove rooted correctness, unrooted reduction, and the specializations obtained for infinite/high skip penalties where justified. Document assumptions needed for positive/negative weights and forbiddance.
- Reproduce paper example figures as discriminating executable fixtures. Ensure edge-label/penalty tests include mismatching edge labels, long paths in either/both trees, multiple child branches, zero weights, negative vertex weights and high penalties.

## 6. Rust/Charon/Aeneas development strategy

- Retain the current Rust crate for performance and differential comparison. Build a small proof-friendly `no-PyO3` Rust core exposing validated tree inputs, exact integer weights, explicit `Result`/`Option` and deterministic witness format. Avoid making `f64` behavior the initial theorem target.
- Run a minimal Charon/Aeneas translation spike on finite-tree and matching operations **before** committing to containers, recursion or callback representation; record tool versions and unsupported features.
- Translate the actual Rust functions; do not substitute hand-written Lean counterparts. Establish refinement at each boundary: tree representation, scoring, matching, DP subproblem and final witness.
- Confirm the exact abstract integer proof matches the chosen Rust arithmetic regime (overflow checked or demonstrably bounded). If later adding floating-point support, prove or state a separate approximation/rounding contract.
- Optimize matching and subproblem reuse behind proved interfaces. Measure and verify the actual complexity; do not infer the paper's asymptotic bound from a symbolic score formula.
- Keep Python/NetworkX wrappers thin and validate adapters separately. Both algorithms should be callable from Python only after paper-level core correctness is stable.

## 7. Work packages and acceptance criteria

**D0. Source ledger and baseline.** Pin paper versions; map all definitions, recurrence cases, lemmas, proofs and complexity claims to page/equation numbers. Record current Rust/Python coverage and benchmark commands. Gate: every claim has a source or is labeled a derived extension.

**D1. Fix objective mismatch.** Add the two score counterexamples above and original-paper examples; implement an evaluator independent of the DP that follows Definition 4 exactly. Gate: oracle agrees with hand calculations; tests intentionally expose current Rust discrepancies.

**D2. Shared Lean definitions.** Finite unordered labeled trees, paths, finite weights, valid matchings and witness validity. Gate: multiple small examples + finite search agree with the definitions; no DP definitions in specification modules.

**D3. Verified weighted matching.** Prove the matching primitive's witness and objective optimality; select and implement a translatable matching solver. Gate: Aeneas-generated Lean is related to the independent matching optimum for all well-formed accepted inputs.

**D4. MCSI mathematics and DP.** Prove rooted recurrence and unrooted completeness. Gate: formally proved output optimality against independent maximum over connected-subtree bijections; exhaustive small-tree differential tests.

**D5. MCSI Rust refinement.** Verify actual translated Rust tree DP and witness. Gate: main Rust entry point has a closed proof of valid, maximum-weight correspondence under explicit preconditions.

**D6. LaWeCSE mathematical specification and recurrence.** Formalize topological embedding, disjoint paths, paper scoring, two-state DP and reconstruction. Gate: theorem does not identify witness validity with algorithm states; exact paper examples pass.

**D7. LaWeCSE Rust repair and refinement.** Correct paper-semantic discrepancies, translate implementation and prove optimality of returned embedding. Gate: generated Lean is connected to the same independent LaWeCSE specification.

**D8. Paper-speed optimization and cost proofs.** Implement specialized related/unbalanced matching methods needed for the 2016/2018 claims, prove core invariants, then cost recurrences. Gate: complexity theorem refers to the actual optimized algorithm and assumptions; empirical scaling is also recorded but never used as proof.

**D9. API, benchmarks, and continuous verification.** Python interfaces, build matrix, malformed-input tests, score-mode compatibility, stress tests, reproducible performance baselines and source/theorem ledger refresh. Gate: repeatable release CI with both algorithm families and both paper-level specifications.

Dependencies: D0 and D1 precede D6; D2 precedes D3/D4/D6; D3 precedes acceptance of D4/D6; D4 before D5; D6 before D7; correctness/refinement precedes D8 performance claims. D0-D3 can progress in parallel with the separate Lozano-Valiente mathematics.

## 8. What constitutes completion

- For **each** of the 2016 and 2018 targets, there is a standalone Lean theorem stating witness validity and true maximum weight against a mathematical specification independent of the algorithm.
- The theorem covers generated semantics for the specific Rust source shipped, with explicit assumptions about valid input, scoring, arithmetic, resources and any admissible excluded cases.
- Any claimed `O(n^2 Delta)` or `O(|T||T'| Delta)` result follows from a cost model of the algorithm actually implemented. Simpler baselines may ship with their honest weaker bounds.
- The scoring conventions and topological constraints of both original papers are covered by independent fixtures and differential/oracle checks, including the counterexamples in Section 4.
- Papers, definitions, theorem statements, implementation entry points, test fixtures, proof status and verification commands are indexed in a maintained ledger.

The existence of a compiling Lean file, successful Python/Rust parity checks, or a fast benchmark alone does not satisfy these completion criteria.
