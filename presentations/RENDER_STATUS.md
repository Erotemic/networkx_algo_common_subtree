# Executed presentation increment: 2026-11-16

All four decks render with Manim 0.20.1, Manim Slides 5.7.0, PyMuPDF 1.28.2,
FFmpeg 6.1.1 and TeX Live 2023. The renderer was installed in the isolated
`/tmp/common-subtree-presentations-venv` environment. Main package and Lean
dependencies were not changed.

| Deck | Scenes | Animation builds / PDF pages | Local HTML video references |
| --- | ---: | ---: | ---: |
| Lozano--Valiente | 17 | 68 | 68 |
| Droschinsky | 19 | 73 | 73 |
| Formalization | 15 | 54 | 54 |
| Legacy combined mathematics | 14 | 42 | 42 |

Every referenced video exists, has positive frame count/duration, and has the
expected 854×480 preview dimensions. Each PDF has one numbered 16:9 page per
animation build. All local HTML video references resolve. Exact source/artifact
hashes and environment versions are in [render_evidence.json](render_evidence.json).
Generated media and slides remain Git-ignored.

## Added demonstrations

- `L10ChildSiblingTraversal` follows real first-child and next-sibling links,
  including returning to a pending traversal frame. It distinguishes sibling
  pointers from parent edges and retains original path identities.
- `L11RecurrenceReuse` decomposes one input pair into all three operational
  branches, shows the actual child-state expressions and scores, then reuses
  a previously expanded state. Its didactic memo trace is checked against the
  independent exhaustive contraction oracle, not production DP instrumentation.
- `D14AugmentingPath` flips `b-x-a-y`, replacing weight 8 with weights 7+7.
  It then animates both original-column deletion instances, independently
  checked to have weights 7 and 8. These are illustrative local/family instances;
  the scene does not attribute a generic Hungarian solver to the paper's
  optimized schedule.
- `D15BranchCollision` explicitly rejects two routes sharing skipped vertex x,
  then shows the different freely rooted candidate mapping the branch point
  to x. It preserves the distinction from forcing the original root.

## Review and corrections

Final builds of all 52 unique scenes were inspected, with additional
intermediate-frame review of the new augmentation and collision examples.
Fixes include a traversal halo that preserves node labels, shorter highlighted
edges, spacing between trees and explanatory strips, and a mathematical × for
forbidden matching entries.

The shape slide now uses the pinned paper/Lean vertex-depth convention: the
three-edge chain has depth 4 and one leaf; the star has depth 2 and three
leaves. The 2016 complexity slides retain the exact v4 asymmetric-degree bound
and logarithmic term. The formalization deck uses proof checkpoint `267f35f`:
original-index references are already proved, while optimized production
witness provenance and source-cost adequacy remain open. Model comparison
counts are explicitly distinguished from actual Rust runtime bounds.

All **32** mathematical-example/export tests pass. LaTeX preflight passed for
the three standalone decks; the subsequent changed expressions also compiled
in their actual scenes. To reproduce from the repository root:

```bash
python -m pip install -r presentations/requirements.txt
python presentations/render.py --check
for deck in lozano droschinsky formalization mathematics; do
    python presentations/render.py --deck "$deck" --html --pdf -q l
done
```

The review covers low-resolution frames and native export artifacts, not a
live audience pacing trial or a browser navigation session. The controlled
two-language application pilot, contemporary baseline comparison and any
publication decision remain open in [RESEARCH_AGENDA.md](RESEARCH_AGENDA.md).
