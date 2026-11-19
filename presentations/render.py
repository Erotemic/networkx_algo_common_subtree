#!/usr/bin/env python3
"""Build the click-advanced common-subtree Manim Slides deck.

The export contract follows the ORIGINAL pre-narration DKPS Manim Slides
builder, introduced in AIQ-Kitware/aiq-dkps-formalization commit 6f3d23d.
Render native Manim Slides fragments, then convert directly to Reveal.js.
No application shell, lecture server, or visible video controls.
The native HTML and PDF include build/page indices; --classic-html and
--classic-pdf preserve the earlier chapter gallery and storyboard exports.

Examples (from repository root)::

    python3 presentations/render.py --html --pdf -q l
    python3 presentations/render.py --scenes OrderedContraction --html --pdf -q h
    python3 presentations/render.py --no-render --html --pdf
    python3 presentations/render.py --scene OrderedRecurrence --html -q l

The presentation is the entire page. Click anywhere for the next build, or use
right/left arrow keys. Output is presentations/renders/<deck>.html.
Do not open presentations/media/<deck>.html (obsolete custom video viewer).
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from html.parser import HTMLParser
from pathlib import Path
import re
import shutil
import subprocess
import sys

from deck import MATHEMATICS, DECKS

HERE = Path(__file__).resolve().parent
ACTIVE_DECK = MATHEMATICS
SCENES = MATHEMATICS.scenes  # backwards compatibility for existing tests
SLIDES_FOLDER = f"slides-{MATHEMATICS.slug}"
RENDERS = HERE / "renders"


def execute(args: list[str], *, cwd: Path = HERE) -> None:
    print("+", " ".join(args), flush=True)
    subprocess.run(args, cwd=cwd, check=True, env={**os.environ, "SUBTREE_PRESENTATION_SLUG": ACTIVE_DECK.slug})


def native_slide_render_command(name: str, quality: str, fps: float | None = None) -> list[str]:
    """DKPS uses the Python module command and long quality syntax."""
    if name not in SCENES:
        raise ValueError(f"Unknown scene: {name}")
    result = [sys.executable, "-m", "manim_slides", "render", f"--quality={quality}"]
    if fps is not None:
        result.append(f"--fps={fps:g}")
    return result + [ACTIVE_DECK.module_for(name), name]


def export_path(suffix: str) -> Path:
    if suffix not in ("html", "pdf"):
        raise ValueError(f"Unsupported export: {suffix}")
    # A new, explicit filename prevents accidentally opening the old custom
    # media/*.html player and interpreting it as a new render.
    return RENDERS / f"{ACTIVE_DECK.slug}.{suffix}"



def number_native_pdf_pages(pdf: Path) -> None:
    """Stamp page indices on *native Manim Slides* PDF builds.

    Reveal.js numbers animation builds on screen. PDF export produces one
    page per build, so the same locating aid needs to be added after conversion.
    Never touch the separate classic storyboard PDF.
    """
    try:
        import fitz
    except ImportError as exc:
        raise RuntimeError(
            "PyMuPDF is required for native PDF page numbers; "
            "install -r presentations/requirements.txt"
        ) from exc
    from tempfile import NamedTemporaryFile
    import os

    with fitz.open(pdf) as doc:
        total = len(doc)
        if total == 0:
            raise ValueError(f"Native PDF has no pages: {pdf}")
        for index, page in enumerate(doc, 1):
            number = f"{index} / {total}"
            rect = page.rect
            size = max(10, min(16, rect.width * .014))
            width = fitz.get_text_length(number, fontname="helv", fontsize=size)
            right = rect.x1 - rect.width * .025
            baseline = rect.y1 - rect.height * .026
            page.insert_text(
                (right - width, baseline), number, fontname="helv",
                fontsize=size, color=(.61, .70, .78), overlay=True,
            )
        # PyMuPDF cannot replace a document while the original handle is open.
        with NamedTemporaryFile(prefix="subtree-pages-", suffix=".pdf",
                                dir=pdf.parent, delete=False) as temp:
            tmp = Path(temp.name)
        try:
            doc.save(tmp, garbage=3, deflate=True)
        except BaseException:
            tmp.unlink(missing_ok=True)
            raise
    os.replace(tmp, pdf)

def native_slide_export_command(names: tuple[str, ...], suffix: str,
                                *, one_file: bool = False,
                                offline: bool = False) -> list[str]:
    """Match the successfully used DKPS ``manim_slides convert`` contract."""
    if not names or any(name not in SCENES for name in names):
        raise ValueError("Export requires known, nonempty scene roster")
    if suffix == "html" and one_file and offline:
        raise ValueError(
            "Do not combine --one-file and --offline: inlining the complete "
            "JavaScript runtime can produce malformed HTML. Use --offline "
            "with linked assets, or --one-file with CDN-hosted libraries."
        )
    cmd = [sys.executable, "-m", "manim_slides", "convert"]
    if suffix == "html":
        # Reproduce the ORIGINAL DKPS default: native Reveal.js HTML with
        # external scripts/styles and sibling video assets. No large inline
        # minified JavaScript bundle and no custom viewer.
        if one_file:
            cmd.append("--one-file")
        if offline:
            cmd.append("--offline")
    cmd += ["--folder", SLIDES_FOLDER, "--to", suffix,
            *names, str(export_path(suffix))]
    if suffix == "html":
        cmd += ["-cslide_number=true", "-ccontrols=false", "-cprogress=false"]
    return cmd


class _NativeHtmlCheck(HTMLParser):
    """Detect JS bundles accidentally exposed as ordinary page text."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.raw_tag = None
        self.exposed_code: list[str] = []
        self.seen_reveal = False

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag in ("script", "style"):
            self.raw_tag = tag
        if tag == "div" and any(k == "class" and "reveal" in (v or "").split()
                                for k, v in attrs):
            self.seen_reveal = True

    def handle_endtag(self, tag: str) -> None:
        if tag == self.raw_tag:
            self.raw_tag = None

    def handle_data(self, data: str) -> None:
        if self.raw_tag is not None:
            return
        chunk = data.strip()
        if (len(chunk) > 2000 and ("function " in chunk or "=>" in chunk)) or \
           ("function t(){return{async:" in chunk):
            self.exposed_code.append(chunk[:120])


def verify_native_html_document(html: str) -> None:
    check = _NativeHtmlCheck()
    check.feed(html)
    if not check.seen_reveal:
        raise ValueError("HTML export is missing the Reveal.js presentation canvas")
    if check.exposed_code:
        raise ValueError(
            "HTML contains JavaScript rendered as page text. Re-export without "
            "combining --one-file and --offline. First snippet: "
            + repr(check.exposed_code[0])
        )


def make_html_presentation_bare(path: Path) -> None:
    """Keep Manim Slides/Reveal.js itself, adding only click-to-advance.

    The exporter owns the markup, video backgrounds, player timing and
    keyboard navigation. The small post-conversion amendment is deliberately
    restricted to hiding Reveal chrome and forwarding left mouse clicks.
    It does not create an iframe, a media player or a second navigation app.
    """
    html = path.read_text(encoding="utf-8")
    if 'id="subtree-fullscreen-click-advance"' in html:
        return
    verify_native_html_document(html)
    body_end = re.search(r"</body\s*>\s*</html\s*>\s*\Z", html, re.IGNORECASE)
    if body_end is None:
        raise ValueError("Manim Slides HTML has no terminal body/html closing tags")
    injection = r"""
<style id="subtree-fullscreen-slide-style">
  html, body { width:100%; height:100%; padding:0; margin:0; overflow:hidden; background:#0E1319; }
  .reveal .controls, .reveal .progress,
  .reveal .playback, .reveal .pause-overlay, .reveal .speaker-notes { display:none !important; }
  .reveal .slide-number { display:block !important; right: 1.15rem; bottom: 0.80rem;
    background:transparent !important; color:#9DB3C8 !important;
    font-size:16px !important; font-family:DejaVu Sans,sans-serif;
    opacity:0.90; pointer-events:none; }
  video::-webkit-media-controls { display:none !important; }
</style>
<script id="subtree-fullscreen-click-advance">
(function () {
  function advance(event) {
    if (event.button !== 0 || event.defaultPrevented) return;
    if (event.target.closest && event.target.closest('a,button,input,select,textarea,[contenteditable]')) return;
    if (typeof Reveal === 'undefined' || !Reveal.next) return;
    event.preventDefault();
    Reveal.next();
  }
  document.addEventListener('click', advance);
  // Keep media elements as background animations, never native players.
  function hidePlayerControls() {
    document.querySelectorAll('video').forEach(function (video) {
      video.controls = false;
      video.removeAttribute('controls');
    });
  }
  document.addEventListener('DOMContentLoaded', hidePlayerControls);
  if (document.readyState !== 'loading') hidePlayerControls();
})();
</script>
"""
    result = html[:body_end.start()] + injection + "\n" + html[body_end.start():]
    verify_native_html_document(result)
    path.write_text(result, encoding="utf-8")


def verify_slide_metadata(names: tuple[str, ...]) -> None:
    """Don't export a partial/old deck as if every chapter was rendered."""
    directory = HERE / SLIDES_FOLDER
    for scene in names:
        metadata = directory / f"{scene}.json"
        if not metadata.is_file():
            raise FileNotFoundError(
                f"Missing Manim Slides metadata for {scene}: {metadata}. "
                "Render it first (omit --no-render)."
            )
        payload = json.loads(metadata.read_text(encoding="utf-8"))
        if not isinstance(payload.get("slides"), list) or not payload["slides"]:
            raise ValueError(f"Slide scene {scene} has no build fragments: {metadata}")


def continuous_render_command(name: str, quality: str) -> list[str]:
    return [sys.executable, "-m", "manim", f"--quality={quality}", "--format", "mp4",
            "--media_dir", str(HERE / "media"), "-o", f"{name}.mp4",
            ACTIVE_DECK.module_for(name), name]


def stitch_videos(names: tuple[str, ...], *, dry_run: bool = False) -> None:
    if dry_run:
        print("+ ffmpeg concat (from continuous Manim MP4 chapters)")
        return
    found = []
    for scene in names:
        matches = sorted((HERE / "media").rglob(scene + ".mp4"),
                         key=lambda p: p.stat().st_mtime)
        if not matches:
            raise FileNotFoundError(f"No continuous MP4 for {scene}")
        found.append(matches[-1])
    directory = HERE / "media"
    directory.mkdir(parents=True, exist_ok=True)
    manifest = directory / "lecture-concat.txt"
    manifest.write_text("".join("file '" + str(path).replace("'", "'\\''") + "'\n"
                                for path in found))
    output = directory / f"{ACTIVE_DECK.slug}.mp4"
    execute(["ffmpeg", "-y", "-f", "concat", "-safe", "0", "-i", str(manifest),
             "-c:v", "libx264", "-pix_fmt", "yuv420p", "-crf", "18", str(output)])


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--deck", choices=tuple(DECKS), default="mathematics",
                        help="standalone lecture (old combined talk remains under mathematics)")
    parser.add_argument("--list", action="store_true", help="list scenes in deck order")
    parser.add_argument("--check", action="store_true", help="run source-level unit tests")
    parser.add_argument("--check-tex", action="store_true", help="preflight all MathTex expressions")
    parser.add_argument("--scene", help="preview one scene from --deck")
    parser.add_argument("--scenes", nargs="+",
                        help="re-render these scenes, then export the full deck")
    parser.add_argument("--html", action="store_true", help="native Reveal.js slide deck")
    parser.add_argument("--pdf", action="store_true", help="PDF from native slide builds")
    parser.add_argument("--classic-html", action="store_true",
                        help="build the earlier static chapter/narration HTML viewer (under media/)")
    parser.add_argument("--classic-pdf", action="store_true",
                        help="build the earlier vector storyboard PDF (under media/)")
    parser.add_argument("--no-render", action="store_true", help="convert previously rendered scenes")
    parser.add_argument("--one-file", action="store_true", help="embed videos; Reveal.js still uses external CDN scripts")
    parser.add_argument("--offline", action="store_true", help="keep JS/CSS and videos as sibling files for offline viewing")
    parser.add_argument("--linked-assets", action="store_true", help="legacy alias for the default linked-assets HTML output")
    parser.add_argument("-q", "--quality", choices=("l", "m", "h", "k"), default="m")
    parser.add_argument("--fps", type=float, default=None)
    parser.add_argument("--all", action="store_true", help="also render ordinary continuous MP4 scenes")
    parser.add_argument("--stitch", action="store_true", help="stitch continuous MP4 scenes")
    parser.add_argument("--dry-run", action="store_true", help="print build commands")
    args = parser.parse_args(argv)
    global ACTIVE_DECK, SCENES, SLIDES_FOLDER
    ACTIVE_DECK = DECKS[args.deck]
    SCENES = ACTIVE_DECK.scenes
    SLIDES_FOLDER = 'slides-' + ACTIVE_DECK.slug
    if args.scene and args.scene not in SCENES:
        parser.error(f'Unknown scene for {args.deck}: {args.scene}')
    if args.scenes and any(name not in SCENES for name in args.scenes):
        parser.error(f'--scenes contains a scene outside {args.deck}')
    if (args.classic_html or args.classic_pdf) and args.deck != 'mathematics':
        parser.error('Classic exports are supported only for the original mathematics deck')

    if args.list:
        print("\n".join(SCENES))
        return
    if args.check_tex:
        if importlib.util.find_spec("manim") is None:
            parser.error("Manim is required for --check-tex")
        sys.path.insert(0, str(HERE))
        from tex_preflight import check_manim_tex
        # Each talk combines new scenes with selected chapters from scenes.py.
        # Preflight every distinct scene source, including shared chapters.
        for module in dict.fromkeys(ACTIVE_DECK.module_for(scene) for scene in SCENES):
            check_manim_tex(HERE / module)
        return
    if args.check:
        execute([sys.executable, "-m", "unittest", "discover",
                 "-s", "tests", "-v"])
        return

    slides_mode = args.html or args.pdf
    if args.scene and args.scenes:
        parser.error("Use --scene for a single-scene preview OR --scenes to update a full deck")
    if args.scene and args.all:
        parser.error("--all is incompatible with --scene")
    if args.stitch and not args.all:
        parser.error("--stitch requires --all")
    if args.one_file and args.linked_assets:
        parser.error("--one-file conflicts with --linked-assets")
    if args.one_file and args.offline:
        parser.error("--one-file and --offline are incompatible; use linked assets for offline output")
    if args.no_render and not slides_mode:
        parser.error("--no-render requires --html or --pdf")
    if not slides_mode and not args.all and not args.scene and not args.classic_html and not args.classic_pdf:
        parser.error("Select --html, --pdf, --classic-html, --classic-pdf, --scene NAME, or --all")

    chosen = (args.scene,) if args.scene else SCENES
    to_render = (args.scene,) if args.scene else tuple(args.scenes or SCENES)
    if slides_mode:
        if not args.dry_run and importlib.util.find_spec("manim_slides") is None:
            parser.error("Install manim-slides (pip install -r presentations/requirements.txt)")
        if not args.no_render:
            for scene in to_render:
                cmd = native_slide_render_command(scene, args.quality, args.fps)
                print("+", " ".join(cmd)) if args.dry_run else execute(cmd)
        if not args.dry_run:
            verify_slide_metadata(chosen)
            RENDERS.mkdir(parents=True, exist_ok=True)
        for suffix, requested in (("html", args.html), ("pdf", args.pdf)):
            if requested:
                cmd = native_slide_export_command(chosen, suffix,
                                                  one_file=args.one_file,
                                                  offline=args.offline)
                print("+", " ".join(cmd)) if args.dry_run else execute(cmd)
                if not args.dry_run:
                    if suffix == "html":
                        make_html_presentation_bare(export_path(suffix))
                    elif suffix == "pdf":
                        number_native_pdf_pages(export_path(suffix))
                    print("Generated native", suffix.upper(), "slides:", export_path(suffix))

    if args.all or (args.scene and not slides_mode):
        if not slides_mode or args.stitch:
            for scene in chosen:
                cmd = continuous_render_command(scene, args.quality)
                print("+", " ".join(cmd)) if args.dry_run else execute(cmd)
        if args.stitch:
            stitch_videos(chosen, dry_run=args.dry_run)

    # The classic viewer and storyboard PDF remain an explicit, independent
    # route. Do not replace either native export with a static screenshot.
    if args.classic_html or args.classic_pdf:
        cmd = [sys.executable, str(HERE / "export.py")]
        if args.classic_html:
            cmd.append("--html")
        if args.classic_pdf:
            cmd.append("--pdf")
        print("+", " ".join(cmd)) if args.dry_run else execute(cmd)
        if not args.dry_run:
            if args.classic_html:
                print("Generated classic HTML:", HERE / "media" / f"{ACTIVE_DECK.slug}.html")
            if args.classic_pdf:
                print("Generated classic PDF:", HERE / "media" / f"{ACTIVE_DECK.slug}.pdf")

    if slides_mode:
        old = HERE / "media" / f"{MATHEMATICS.slug}.html"
        if old.exists():
            print(f"NOTE: {old} is the classic viewer. The native slide deck is {export_path('html')}.")


if __name__ == "__main__":
    main()
