# Mathematical Manim presentation and prospective application paper

See [`../../presentations/README.md`](../../presentations/README.md) for the
working Manim source, rendering commands, storyboard and mathematical example
tests. See [`../../presentations/RESEARCH_AGENDA.md`](../../presentations/RESEARCH_AGENDA.md)
for the proposed controlled application study.

## Completed first increment

- Source-first Manim chapters on operational ordered contractions, Dyck
  encoding, Lozano–Valiente Lemma 8, weighted unordered matching (2016),
  topological path penalties (2018), and proof/refinement boundaries.
- Source crosswalk to the existing Lean proof files and exact references.
- Executable tiny mathematical examples tested independently of Manim and of
  the project's production Rust/Cython solvers.
- Research agenda naming AST structural alignment as a **candidate** pilot,
  with APTED, GumTree and RefactoringMiner as distinct baselines.

## Executed presentation increment: 2026-11-16

Items 1–4 below are implemented and checked. All four decks render/export at
16:9 (65 scene instances, 237 builds/PDF pages); all 32 presentation tests pass.
The new scenes animate actual child/sibling traversal, all three decomposed
recurrence branches with memo reuse, weighted path augmentation and related
deletion instances, and forbidden skipped-branch collisions. Visual review
also corrected the vertex-depth convention, the precise 2016 v4 degree bound
and proof-assurance wording. Exact scope, commands, versions and artifact
hashes are in [the render report](../../presentations/RENDER_STATUS.md).

This does not complete the application study or establish a novel paper claim.
Current proof assertions were checked against checkpoint `267f35f`; no new
production timing claim was introduced. Items 5–7 remain ongoing requirements.

## Work and acceptance requirements

1. Render every Manim chapter with the local Manim and LaTeX installation;
   inspect at 16:9 and refine animation pacing and mathematical typography.
2. Add a true first-child/next-sibling traversal animation and an animated
   three-branch recurrence decomposition with dynamic-programming state reuse.
3. Add code-backed animation of weighted partial matching, including an
   augmenting-path step and the structurally related instances of the 2016
   optimized algorithm. Avoid depicting a generic Hungarian solver as the
   paper's actual optimized strategy.
4. Add a 2018 skeleton-validity animation that explicitly shows why skipped
   branch-point collisions are forbidden.
5. Track `proofs/PROOF_STATUS.md` and current runtime benchmarks when claiming
   theorem completion, source-level Rust refinement or performance.
6. Perform the application pilot with a pinned benchmark and report failures,
   ambiguity and objective mismatches alongside successes.
7. Decide the paper narrative only after measuring a reproducible novel claim.

Keep original binary media out of Git. Generated videos, PDF frames and the
optional slide exports go under Git-ignored media paths.
