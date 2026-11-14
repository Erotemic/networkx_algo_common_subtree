# Animated mathematical presentation: common subtree algorithms

This is a **source-first Manim presentation**. It teaches the three related
mathematical problems and how the repository's Lean formalization and Rust
implementations relate to them. All tree drawings, matrices and formulae are
programmatically generated. No binary media belongs in the source overlay.

The scene implementation is in [`scenes.py`](scenes.py), with reusable graphics
in [`visuals.py`](visuals.py). [`math_examples.py`](math_examples.py) provides
tiny **independent** executable examples; the slides never depend on running the
production Rust/Cython solver.

## Build

From the repository root:

```bash
cd /home/joncrall/code/networkx_algo_common_subtree
python3 -m venv .venv-manim
. .venv-manim/bin/activate
python -m pip install -r presentations/requirements.txt

# Verify examples and (when Manim is installed) compile all scene mathematics:
python3 presentations/render.py --check

# Recheck only the LaTeX formulas without rendering videos:
python3 presentations/render.py --check-tex

# Render a quick scene to inspect typography and layout:
python3 presentations/render.py --scene OrderedRecurrence --quality l

# Render all independent chapters; generated media are Git-ignored:
python3 presentations/render.py --all --quality h --stitch
```

All scene equations use an explicit `amsmath`/`amssymb` TeX template.
`--check-tex` extracts formulas from the scene source and compiles them with
the installed Manim version. If a mathematical expression fails, it reports
its source line before rendering begins. Prose uses Manim `Text` where possible.

Manim requires a working LaTeX toolchain and the native dependencies appropriate
to your platform. The optional `manim-slides` package supports interactive
playback; absent it, the classes render as ordinary timed Manim scenes.

To use interactive slides, install `manim-slides` separately and render with its
CLI, e.g. `manim-slides render presentations/scenes.py OrderedRecurrence`.
Each scene has several beats and a companion narration in
[`STORYBOARD.md`](STORYBOARD.md). Keep the scene source modular; do not combine
the entire lecture into one giant scene.

**Optional static PowerPoint storyboard:** `npm install --prefix presentations &&
npm run --prefix presentations preview` generates a review deck under
`presentations/media/`. This is not a substitute for the animated Manim
lecture. The preview generator uses PptxGenJS and has no Manim dependency.

## Chapter order

`AllProblems`, `OrderedContraction`, `BalancedWords`,
`DeletionIsContraction`, `OrderedRecurrence`, `CorrectnessAndComplexity`,
`AffinityExtensions`, `WeightedUnorderedMatching`,
`SparseMatchingOptimization`, `TopologicalDistancePenalties`,
`MappedAndSkippedStates`, `ProofBoundary`,
`ApplicationExperiment`, `PaperContribution`.

Run `python3 presentations/render.py --list` for the machine-readable list.

## Mathematical and historical precision

- Lozano–Valiente concerns **ordered rooted tree embedding via edge
  contraction**. The slides use the *operational* containment relation, not the
  literal printed recursive Definition 2, whose discrepancy is documented in
  `docs/planning/lozano_valiente_2004_containment_definition_audit.md`.
- Droschinsky 2016 concerns **weighted, unordered, possibly unrooted subtree
  isomorphism**; the displayed matching formula is the fixed-root subproblem,
  not a claim that the unrooted problem has a single root.
- Droschinsky 2018 concerns **topological embeddings with distance penalties**.
  A direct edge reward applies only when *both* corresponding paths have
  length one. Longer paths incur skip penalties instead.
- Node affinities, token mappings and witness readback are extensions and
  implementation interfaces; they are not being attributed to the 2004 paper.
- A Lean proof of a mathematical recurrence and a source-level refinement of
  a Rust function are separate assurance statements. Consult
  `proofs/PROOF_STATUS.md` at the actual checkout before changing proof badges.

## Paper investigation

[`RESEARCH_AGENDA.md`](RESEARCH_AGENDA.md) proposes an application pilot,
baselines, metrics, threats to validity, and a conservative path toward a
research contribution. The deck intentionally makes **no unsupported SOTA or
performance-win claim**.

[`REFERENCES.md`](REFERENCES.md) ties the lecture to the original papers,
Lean modules, and candidate application baselines.

## Test status of this overlay

The dependency-free examples and their 529-pair recurrence/oracle comparison
run without Manim. The generated scene source is syntax-checked, but **Manim
itself was not available in the authoring environment**, so video rendering and
visual acceptance must be run locally before presenting publicly. Do not treat
an unrendered scene as visually verified.
