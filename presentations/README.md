# Common subtree mathematics: click-through Manim presentation

This deck deliberately uses the **original, pre-narration DKPS presentation workflow**:
Manim scenes inherit `manim_slides.Slide`; each `next_slide()` separates
one mathematical animation build; `manim_slides convert` creates a native
Reveal.js HTML presentation. Reference:
[the first DKPS slide builder](https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/6f3d23d7d4dab5e36e0cb738d2eb5d91958fdaf0/visualizations/dkvis/build_slides.py).

## What opens in the browser

The **native presentation** fills the page. Click anywhere to advance one
build, or use right/left arrows to move forward/back. It has no navigation
shell, embedded video player or progress bar. A small **slide number at the
bottom right** makes it possible to report layout issues by build. The native
PDF numbers all its pages as well. MP4 fragments are used internally by
Reveal.js as animated slide backgrounds.

The **classic presentation** is an optional separate HTML gallery (static
slides, chapter picker, narration, and optional embedded MP4 player). The
classic storyboard PDF remains available. Neither export replaces the other.

## Build

From the repository root, using the Manim Python environment:

```bash
python3 -m pip install -r presentations/requirements.txt
python3 presentations/render.py --check
python3 presentations/render.py --check-tex
python3 presentations/render.py --html --pdf --quality l
xdg-open presentations/renders/common-subtree-mathematics.html

# Optional old chapter/notes viewer and its static PDF
python3 presentations/render.py --classic-html --classic-pdf
xdg-open presentations/media/common-subtree-mathematics.html
```

Render at 1080p when the draft is reviewed:

```bash
python3 presentations/render.py --html --pdf --quality h
```

The default HTML follows the **original pre-narration DKPS export**: a
full-viewport Reveal.js presentation with linked video assets and CDN-hosted
Reveal.js scripts. The browser must be online to load the JavaScript when
using this default mode. Use `--offline` to download the JavaScript/CSS and
videos into the presentation's neighboring assets directory, which must travel
with the HTML file. Use `--one-file` only if a standalone HTML with embedded
videos is specifically needed; in this mode JavaScript is still CDN-hosted.
Do not combine `--one-file` and `--offline`: inline minified JavaScript has
previously produced malformed HTML that displayed library source as slide text.
The native PDF uses the same Manim Slides fragments, with one numbered page
per build. The smaller slide numbers in the native HTML come from Reveal.js.
Long Manim scene headings are fitted to the slide width; a header-divider
assertion rejects content that would collide with the diagram area.

Both HTML formats are intentional, but **open the right one**:

- `presentations/renders/common-subtree-mathematics.html`: native, full-page,
  click-to-advance (default `--html`).
- `presentations/media/common-subtree-mathematics.html`: earlier classic
  chapter/notes viewer (generated only with `--classic-html`).

`--classic-html` rebuilds the old static PDF first, using the PptxGenJS
storyboard and LibreOffice, then embeds its page images into HTML. This needs
Node.js (`npm install --prefix presentations` once), LibreOffice and either
PyMuPDF or Poppler. It does **not** need Manim. `--classic-pdf` exports only
that earlier storyboard PDF. You can combine `--html --pdf --classic-html
--classic-pdf` to produce all four outputs.

To preview just the recurrence chapter:

```bash
python3 presentations/render.py --scene OrderedRecurrence --html --quality l
```

Once a full deck exists, update selected chapters without recomputing the rest:

```bash
python3 presentations/render.py --scenes OrderedContraction BalancedWords --html --pdf --quality h
```

Only re-export existing fragments:

```bash
python3 presentations/render.py --no-render --html --pdf
```

The native builder directly calls `manim_slides render` then
`manim_slides convert`. A small HTML post-processing step hides Reveal
controls and maps a plain left mouse click to `Reveal.next()`, while keeping
Reveal's slide number. Native PDF pages are numbered by PyMuPDF immediately
after conversion. The classic outputs use the preserved `export.py`.

## Mathematical content

The 14 chapters cover ordered edge contraction, Dyck encoding, the 2004
recurrence, node affinities and witnesses, 2016 weighted unordered child
matching, 2018 topological-path penalties, and formal verification. The
central examples now advance one relevant operation per click. The numerical
examples live in `math_examples.py`, independent of presentation rendering,
and have an exhaustive small-tree oracle in `tests/test_examples.py`.

`STORYBOARD.md` records extended mathematical explanation; `RESEARCH_AGENDA.md`
records application-study hypotheses; `REFERENCES.md` records paper references.
These are supplementary source materials rather than a second lecture viewer.

## Validation

`python3 presentations/render.py --check` verifies the source-level examples,
export commands, page-numbering logic, and minimal HTML adaptation. `--check-tex` checks TeX with
Manim installed. Inspect actual HTML slide transitions and the PDF on a local
Manim installation before sharing; this source overlay cannot contain a
verified video render from the present environment.

### Quick repair of an already-rendered native deck

If the HTML displays minified JavaScript source as text, skip the expensive
Manim rendering and re-export the slide fragments:

```bash
python3 presentations/render.py --no-render --html
xdg-open presentations/renders/common-subtree-mathematics.html
```

To view offline, instead run `python3 presentations/render.py --no-render --html --offline`
and keep the generated HTML and sibling asset directory together.
