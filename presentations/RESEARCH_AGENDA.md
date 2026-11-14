# From a verified algorithm collection to a defensible research contribution

**Status:** candidate research program, not a publication or a demonstrated
SOTA result. The 2004, 2016, and 2018 algorithms are prior work; the proposed
contribution must be specified separately from their reproduction.

## 1. What the project can claim today (subject to source/build audit)

- The repository contains mathematical specifications and substantial Lean
  proofs of the operational Lozano–Valiente recurrence, tree/Dyck equivalence,
  weighted matching, and Droschinsky recurrences. Consult the exact
  `proofs/PROOF_STATUS.md` in the *current* checkout, not a narrative summary.
- It contains optimized and reference Rust implementations, PyO3 integration
  for some ordered variants, and Cython/Python alternatives. Some verified
  Rust cores are still slower or less feature-complete than older backends.
- The 2018 scoring mismatch and the printed 2004 containment discrepancy were
  identified and documented in the repository. Whether these observations
  support a new mathematical result or a corrected implementation note needs
  a detailed literature review and careful attribution.
- It has **not** yet demonstrated a public application win over a contemporary
  state-of-the-art competitor.

## 2. Primary application pilot: matching changed program structure

**Hypothesis:** On some kinds of structured code edits, an ordered common
embedded-subtree objective with typed affinities will find accurate reusable
substructures, especially when wrappers or intermediate syntax nodes are
inserted, at competitive latency for medium-size ASTs.

**Inputs:** paired source trees from real revisions. Parse them with a fixed
Tree-sitter grammar version. Represent only a well-defined rooted ordered AST
subset; keep a correspondence from parser nodes to source ranges. Decide
explicitly whether punctuation, anonymous nodes, comments and language-specific
syntactic sugar appear in the tree.

**Reference labels:** reviewed node correspondences where available, including
the AST mapping benchmark associated with the RefactoringMiner 2024 work.
Validate dataset availability and reuse rights before adopting it. Separate
mapping-quality evaluation from the ability to generate human-readable edit
scripts, since an exact common subtree is not an edit script by itself.

**Baselines** (distinct objectives; compare on shared downstream metrics):

1. **APTED:** optimal ordered tree edit distance plus edit mappings.
2. **GumTree (recent version):** heuristic AST mapping/diff; record exact
   algorithm version, configuration, and treatment of AST node labels.
3. **RefactoringMiner AST mappings:** a refactoring-aware contemporary mapping
   reference, where inputs and supported languages overlap.
4. **In-repository controls:** pure Python, Cython, optimized Rust, and verified
   Rust implementing the **same** common-embedding contract.
5. **Ablations:** labels only; structure only; node-affinity features; witness
   backtracking; sparse matching optimizations where applicable.

**Primary experimental outcomes:** mapping precision/recall/F1 under a documented
annotation policy; wall-clock latency for complete pipeline; maximum resident
memory; and coverage/failure rate. If the use case is retrieval rather than
edit mapping, predeclare recall@k and mAP on a held-out labeled corpus.

**Comparability rule:** Do not compare raw maximum-common-subtree scores to tree
edit distances as if they were calibrated probabilities or identical objectives.
When a baseline can solve exactly the same objective, use score/witness parity;
when it solves another objective, use downstream metrics with common inputs.

**Stratification:** AST size (nodes and height), max degree, percentage of
inserted wrapper nodes, changed-node fraction, language, and project. Report
results by strata, not only aggregates. Measure parsing and conversion both
included and excluded, but make end-to-end time the primary deployment metric.

**Pilot gate:** choose two languages and a small, fixed evaluation subset before
optimizing. Keep a dedicated held-out set, and run a paired significance
analysis or uncertainty interval across files/projects rather than treating
correlated edits as independent samples. Report negative findings.

## 3. Alternative applications to assess

- **LLM-generated code revision and patch localization.** The same AST task
  can focus on generated edits. Evaluate whether alignment improves downstream
  patch review or automated diagnosis; compare with contemporary tools and
  account for the cost of the generator, if included.
- **Tree-shaped configuration/document schemas.** XML/JSON tree changes or
  hierarchical UI layouts have naturally ordered structure. Compare with APTED
  and practical diff tools. Establish a labeled dataset before claiming value.
- **Chemical and phylogenetic trees.** More faithful to Droschinsky's intended
  applications in the papers, but requires reliable domain-specific input
  labels and comparisons to specialist tools. Avoid treating general molecular
  graphs or phylogenetic networks as trees without an explicit reduction.

Choose **one** application for the first paper pilot. Breadth without a strong
controlled experiment weakens the result.

## 4. What would constitute novelty?

| Possible contribution | Required new evidence | Common failure mode |
| --- | --- | --- |
| Verified implementation | End-to-end source/function refinement, sound specifications, executable proof audit | Only a separately formalized reference algorithm is proved |
| Algorithm engineering | Reproducible improvements over tuned native/algorithmic baselines and complexity analysis where claimed | Rust beats Python only; native comparator omitted |
| Extension theory | New, independently specified weighting/affinity or constraint model with correctness/complexity theorem | Rebranding old weighted matching as new |
| Empirical application | Public task, held-out data, quality gain or compelling Pareto tradeoff | Cherry-picked examples and incomparable objective scores |
| Corrected source statement | Exact historical review, proof of discrepancy, treatment of prior corrections | Claiming the original authors' intended theorem is newly discovered |

A conference-style contribution may combine these, but the abstract should
be written only after evidence supports a specific thesis.

## 5. Performance and verification experiment plan

For each paper family and implemented extension, record:

- **Mathematical contract:** order/rootedness, labels, permissible omissions,
  edge/path score, negative weights, numeric domain, returned witness.
- **Equivalent algorithm backends:** pure Python, Cython, optimized Rust,
  verified Rust; compare scores and independently rescore witnesses.
- **Exact small oracle:** exhaustive contraction or mapping/matching on small
  inputs. Disagreement is a correctness failure until investigated.
- **Shape regimes:** chains, stars/high-degree trees, balanced trees, skewed
  trees, mixed sizes, realistic application-derived trees.
- **Metrics:** median or distribution of latency over repeated trials, max RSS,
  allocations if available, optional CPU counters, accuracy/quality on a
  labeled downstream application.
- **Reproducibility:** source SHA, OS/CPU, Python/Rust/Lean versions, compiler
  flags, build provenance, benchmark data, raw per-case results and plotting
  script. Pre-register machine and warm-up policy.
- **Statistical reporting:** paired per-case ratios and uncertainty intervals,
  avoid single aggregate speedup on dissimilar tree distributions.

**Formalization boundary:** Identify precisely whether the theorem covers
mathematical recurrence, Rust source code, optimized path, input validation,
output serialization, numeric overflow, witness readback, and external Python
callable affinities. Preserve the gaps in the assurance ledger.

## 6. Implementation sequence and stop/go decisions

1. **Runnable software:** finish Python/PyO3 access to the intended ordered and
   Droschinsky variants. A reference Rust implementation can be exposed before
   optimization is complete.
2. **Correctness parity:** wire strict independently validated tests for each
   public mode; the Cython source is evidence of intent, not an oracle.
3. **Performance baseline:** gather Cython/legacy-Rust/verified-Rust timings on
   identical inputs and compare with published/available native competitors.
4. **Application pilot:** measure mapping quality on fixed annotated code-edit
   pairs. If this has no application advantage, explore another fit or make the
   implementation-and-verification contribution the paper's core.
5. **Complete proof and optimized implementation:** the eventual verified
   release needs the actual production paths covered. Do not delay usable
   development builds on every remaining theorem.
6. **Paper decision:** formulate the precise claim after seeing application
   metrics, runtime scaling, and assurance status. Consider algorithm
   engineering, formal methods, or applied software engineering venues based
   on what evidence is strongest.

## 7. Closest work and sources to study

- Lozano and Valiente (2004), *On the Maximum Common Embedded Subtree Problem
  for Ordered Trees*: https://www.cs.upc.edu/~antoni/subtree.pdf
- Droschinsky, Kriege, Mutzel (2016), *Faster Algorithms for the Maximum Common
  Subtree Isomorphism Problem*: https://doi.org/10.4230/LIPIcs.MFCS.2016.33
- Droschinsky, Kriege, Mutzel (2018), *Largest Weight Common Subtree Embeddings
  with Distance Penalties*: https://doi.org/10.4230/LIPIcs.MFCS.2018.54
- Pawlik and Augsten, APTED: https://github.com/DatabaseGroup/apted
- GumTree project and the 2024 source-differencing analysis:
  https://github.com/GumTreeDiff/gumtree and
  https://doi.org/10.1145/3597503.3639148
- Refactoring-aware AST mapping dataset and evaluation (2024):
  https://arxiv.org/abs/2403.05939
- Tree-sitter parser documentation: https://tree-sitter.github.io/tree-sitter/

These are candidate baselines, not proof that our approach outperforms them.
