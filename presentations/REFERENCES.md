# Source map for the lecture

## Primary mathematics

1. Antoni Lozano and Gabriel Valiente (2004), *On the Maximum Common Embedded
   Subtree Problem for Ordered Trees*,
   https://www.cs.upc.edu/~antoni/subtree.pdf.
   Scene usage: ordered contractions, balanced words, Lemma 8 three-way
   recurrence and the published complexity target.
2. Andre Droschinsky, Nils M. Kriege, Petra Mutzel (2016), *Faster Algorithms
   for the Maximum Common Subtree Isomorphism Problem*, MFCS 2016,
   https://doi.org/10.4230/LIPIcs.MFCS.2016.33.
   The complexity slides use the repository's pinned
   https://arxiv.org/pdf/1602.07210v4, Theorem 4:
   `O(|G|*|H|*(min(DeltaG,DeltaH)+log(max(DeltaG,DeltaH))))`.
   Scene usage: rooted child matching and related matching instances. The
   logarithmic term and asymmetric degrees are retained explicitly.
3. Andre Droschinsky, Nils M. Kriege, Petra Mutzel (2018), *Largest Weight
   Common Subtree Embeddings with Distance Penalties*, MFCS 2018,
   https://doi.org/10.4230/LIPIcs.MFCS.2018.54.
   Scene usage: topological skeleton, path penalties, direct-edge scoring rule.

## Current project formalization (267f35f / 2026-11-16 proof checkpoint)

- `proofs/SubtreeProofs/Paper2004/OrderedTree.lean`
- `proofs/SubtreeProofs/Paper2004/EncodingEquivalence.lean`
- `proofs/SubtreeProofs/Paper2004/ContractionCompleteness.lean`
- `proofs/SubtreeProofs/Paper2004/DynamicProgram.lean`
- `proofs/SubtreeProofs/Paper2004/Decomposition.lean`
- `proofs/SubtreeProofs/Paper2004/TreeStateBounds.lean` — depth counts vertices,
  with singleton depth one; actual leaves, including the singleton leaf.
- `proofs/SubtreeProofs/Rust/LookupEvents.lean` — packet-model bounds and value
  erasure; source-event adequacy remains open.
- `proofs/SubtreeProofs/Droschinsky2016/RootedRecurrence.lean`
- `proofs/SubtreeProofs/Droschinsky2018/Specification.lean`
- `proofs/PROOF_STATUS.md` — exact current assurance status; update when source
  changes, don't hardcode green proof badges in Manim.
- `docs/planning/lozano_valiente_2004_containment_definition_audit.md` —
  printed Definition 2 discrepancy and an operational counterexample.

## Application and baseline references

- APTED (Pawlik and Augsten), https://github.com/DatabaseGroup/apted.
  Exact ordered labeled tree edit distance; different target objective.
- GumTree, https://github.com/GumTreeDiff/gumtree.
  Practical AST mapping and differencing.
- Falleri and Martinez (2024), *Fine-grained, accurate and scalable source
  differencing*, https://doi.org/10.1145/3597503.3639148.
  Contemporary source differencing performance and mapping quality.
- Alikhanifard and Tsantalis (2024), *A Novel Refactoring and Semantic Aware
  Abstract Syntax Tree Differencing Tool and a Benchmark for Evaluating the
  Accuracy of Diff Tools*, https://arxiv.org/abs/2403.05939.
- Tree-sitter, https://tree-sitter.github.io/tree-sitter/.
  Parser for producing ordered syntax trees.

**Reference policy:** The lecture should visually distinguish published prior
results, current independently proved declarations, and original new claims
still under experimental investigation. For conference submission, verify
bibliographic editions and exactly which publication/version each formula
follows. Do not use Matplotlib screenshots or external copyrighted figures:
all Manim diagrams here are original constructions.
