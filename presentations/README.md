# Common subtree mathematics: three standalone animated presentations

Three talks are built with the **original DKPS-style Manim Slides workflow**.
Each animation beat is a native `manim_slides.Slide` fragment; browser output is
just the full-window Reveal.js canvas with click/arrow navigation and a small
slide number. No player buttons, lecture website, or embedded custom viewer.
All three decks can be opened independently and contain their own definitions,
examples, proof ideas, and conclusions.

| Deck key | Slides/scenes | Scope |
| --- | ---: | --- |
| `lozano` | 15 | Lozano--Valiente 2004: ordered contraction, Dyck encodings, first-return decomposition, printed containment counterexample, three-branch recurrence, structural witnesses, memoization and tree-shape-sensitive complexity |
| `droschinsky` | 17 | Droschinsky--Kriege--Mutzel 2016 and 2018: weighted unordered isomorphism, matching, root selection, dummy assignments, dual search and reuse, topological paths, skip penalties and mapped/skipped states |
| `formalization` | 15 | Mathematical specifications, proved trees-to-Dyck equivalence, recurrence proofs and counterexample, source-derived Lean/Rust correctness via Aeneas, matching, test oracles and remaining optimized graph obligations |

The previous 14-scene combined `mathematics` presentation is retained as a
fourth **legacy** deck, and the earlier static gallery remains available through
`--deck mathematics --classic-html` and `--classic-pdf`. These options do not
replace the three new talks.

## Setup and render all three

From the repository root, in the Python environment used for Manim:

```bash
python3 -m pip install -r presentations/requirements.txt
python3 presentations/render.py --check

for deck in lozano droschinsky formalization; do
    python3 presentations/render.py --deck "$deck" --html --pdf -q l
done
```

Open the complete decks (NOT the earlier `presentations/media/*.html` files):

```bash
xdg-open presentations/renders/lozano-valiente-2004.html
xdg-open presentations/renders/droschinsky-2016-2018.html
xdg-open presentations/renders/common-subtree-formalization.html
```

Native PDFs share the exact same base paths, with `.pdf` instead of `.html`.
There is a page number in the lower-right corner of the HTML and each PDF
page. Click to advance a mathematical build; left/right arrows also navigate.

For the full-resolution version, replace `-q l` with `-q h`. For a single
scene preview:

```bash
python3 presentations/render.py --deck lozano --scene L05ValueTrace --html -q l
```

That preview replaces the *Lozano* HTML with a one-scene preview. Restore the
complete deck afterwards by rebuilding it, or by running the complete
`--no-render --html` export after its other scenes already exist. To update
selected scenes in an existing full deck and reconvert all fragments:

```bash
python3 presentations/render.py --deck droschinsky \
    --scenes D11DualCut D12DeletionReuse --html --pdf -q h
```

After all scenes are rendered, exporting alone is much faster:

```bash
python3 presentations/render.py --deck formalization --no-render --html --pdf
```

The default HTML follows the working DKPS convention: Reveal.js JavaScript
comes from its CDN and videos live in a sibling assets directory. For a deck
that works with no network access, use `--offline`; transfer that directory
along with the HTML. The known problematic `--one-file --offline` combination
is refused. The HTML viewer itself has no visible playback bar.

## Build structure

- `deck.py` declares the four independent scene orders, filenames, and the
  scene file in which each class is defined.
- `lozano_scenes.py`, `droschinsky_scenes.py`, and `formalization_scenes.py`
  contain the new mathematical material and per-animation spoken notes.
- `scenes.py` retains existing scenes and shared `MathPresentation` layout;
  the deck slug selects a separate `slides-<slug>/` metadata directory.
- `lecture_primitives.py` supplies small, predictable Manim composition
  functions; the independently checked examples are in `math_examples.py`.
- `render.py` invokes the installed Manim Slides render and HTML/PDF converters,
  without adding a web server or a second player layer.

Manim is **not** installed in the artifact-authoring environment where this
source patch was prepared. Syntax, example values, LaTeX snippets, source
registration, and all source-only tests were checked, but visual rendering
still needs local inspection. `--check-tex` on your installed Manim environment
will run its full LaTeX preflight for the chosen deck:

```bash
python3 presentations/render.py --deck lozano --check-tex
python3 presentations/render.py --deck droschinsky --check-tex
python3 presentations/render.py --deck formalization --check-tex
```

## Scope of the mathematics

Lozano and Valiente (2004) prove an ordered common embedded subtree algorithm.
The presentation distinguishes their literal printed Definition 2 from the
operational matched-pair deletion relation: the repository's Lean theorem proves
they differ on `001011 -> 0011` while the operational three-branch recurrence
is proved correct. Node-affinity and isomorphism options in the maintained
library are additional contracts, not attributed verbatim to that paper.

Droschinsky, Kriege and Mutzel (MFCS 2016) treat weighted maximum common
subtree *isomorphism* of unordered, unrooted trees. Their MFCS 2018 model
allows path embeddings and penalties for skipped vertices. The fast bounds
belong to the published algorithms; the current repo has independently proved
reference recurrences and some exact Rust matching machinery, but does **not**
yet certify the full optimized graph solver or those published runtime bounds.

Formalization status is intentionally pinned to the provided **2026-11-14**
repository snapshot (`proofs/PROOF_STATUS.md`). The deck separates theorems
about independent specifications, translated safe Rust entry points, operation
bounds, float API conventions, and finite regression tests.

## Primary sources

- Antoni Lozano and Gabriel Valiente, *On the Maximum Common Embedded Subtree
  Problem for Ordered Trees* (2004): https://www.cs.upc.edu/~antoni/subtree.pdf
- Andre Droschinsky, Nils M. Kriege, Petra Mutzel, *Faster Algorithms for the
  Maximum Common Subtree Isomorphism Problem* (MFCS 2016):
  https://doi.org/10.4230/LIPIcs.MFCS.2016.33
- Same authors, *Largest Weight Common Subtree Embeddings with Distance
  Penalties* (MFCS 2018):
  https://doi.org/10.4230/LIPIcs.MFCS.2018.54
- Repository: `proofs/PROOF_STATUS.md`, `proofs/VERIFICATION.md`,
  `docs/planning/paper_statement_crosswalk.md`.
- Original minimal DKPS export implementation:
  https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/6f3d23d7d4dab5e36e0cb738d2eb5d91958fdaf0/visualizations/dkvis/build_slides.py

## Version-control hygiene

Do not commit `presentations/node_modules/`, `presentations/slides-*/`,
`presentations/renders/`, or `presentations/media/`. They are now covered by
`presentations/.gitignore`. If these paths were already tracked by an earlier
commit, `.gitignore` does not untrack them: see the cleanup commands accompanying
this source overlay.
