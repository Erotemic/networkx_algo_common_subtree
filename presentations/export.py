#!/usr/bin/env python3
"""Build offline HTML slides and a 16:9 PDF from the mathematical storyboard.

The PDF uses the PptxGenJS storyboard's vector drawings. The HTML embeds
its slide images and, when present, links to the existing Manim MP4 scenes.
Nothing here depends on Manim itself: static exports work before video renders.

Examples (from repository root):
    python3 presentations/render.py --html --pdf
    python3 presentations/render.py --all --quality h --html --pdf
    python3 presentations/export.py --html --pdf --rebuild-storyboard
"""
from __future__ import annotations

import argparse
import base64
import html
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import quote

HERE = Path(__file__).resolve().parent
MEDIA = HERE / "media"
PDF_NAME = "common-subtree-mathematics.pdf"
HTML_NAME = "common-subtree-mathematics.html"
PPTX_NAME = "common-subtree-storyboard.pptx"
CHAPTER_SCENES = (
    "AllProblems", "OrderedContraction", "BalancedWords", "DeletionIsContraction",
    "OrderedRecurrence", "CorrectnessAndComplexity", "AffinityExtensions",
    "WeightedUnorderedMatching", "SparseMatchingOptimization",
    "TopologicalDistancePenalties", "MappedAndSkippedStates", "ProofBoundary",
    "ApplicationExperiment", "PaperContribution",
)

TRACKS = (
    "Overview", "Lozano-Valiente 2004", "Lozano-Valiente 2004",
    "Lozano-Valiente 2004", "Lozano-Valiente 2004", "Lozano-Valiente 2004",
    "Algorithm extensions", "Droschinsky 2016", "Droschinsky 2016",
    "Droschinsky 2018", "Droschinsky 2018", "Verification",
    "Applications", "Research contributions",
)


@dataclass(frozen=True)
class Chapter:
    scene: str
    title: str
    track: str
    narration: str


def read_chapters() -> list[Chapter]:
    """The storyboard is the narration source; its numbered headings define order."""
    source = (HERE / "STORYBOARD.md").read_text(encoding="utf-8")
    matches = list(re.finditer(r"(?m)^## (\d+)\. ([A-Za-z][A-Za-z0-9]+)\s+[—–-]\s+(.+?)\s*$", source))
    chapters = []
    for idx, match in enumerate(matches):
        number, scene, title = match.groups()
        if int(number) != idx + 1:
            raise ValueError(f"Unexpected storyboard numbering: {number}")
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(source)
        chapters.append(Chapter(scene, title.strip(), TRACKS[idx], source[match.end():end].strip()))
    if tuple(x.scene for x in chapters) != CHAPTER_SCENES:
        raise ValueError("Storyboard chapters diverge from Manim scene order. Update them together.")
    return chapters


def _run(cmd: list[str], *, cwd: Path = HERE) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def _find_executable(name: str) -> str:
    binary = shutil.which(name)
    if binary is None:
        raise RuntimeError(f"Missing '{name}'; install it to build PDF/HTML exports")
    return binary


def build_storyboard(*, force: bool = False) -> Path:
    dest = MEDIA / PPTX_NAME
    src = HERE / "storyboard_preview.js"
    MEDIA.mkdir(parents=True, exist_ok=True)
    if not force and dest.exists() and dest.stat().st_mtime >= src.stat().st_mtime:
        return dest
    _run([_find_executable("node"), str(src)])
    if not dest.is_file():
        raise RuntimeError(f"PowerPoint generator did not create {dest}")
    return dest


def build_pdf(*, rebuild_storyboard: bool = False) -> Path:
    pptx = build_storyboard(force=rebuild_storyboard)
    dest = MEDIA / PDF_NAME
    lo = shutil.which("libreoffice") or shutil.which("soffice")
    if not lo:
        raise RuntimeError("LibreOffice is required for PDF export (install libreoffice-impress)")
    with tempfile.TemporaryDirectory(prefix="subtree-pdf-") as tmp:
        temp = Path(tmp)
        profile = (temp / "lo-profile").as_uri()
        _run([lo, f"-env:UserInstallation={profile}", "--headless", "--convert-to", "pdf",
              "--outdir", str(temp), str(pptx)])
        generated = temp / f"{pptx.stem}.pdf"
        if not generated.exists():
            raise RuntimeError(f"LibreOffice did not produce {generated}")
        shutil.copyfile(generated, dest)
    print("Wrote", dest)
    return dest


def _slide_pngs(pdf: Path, *, width: int = 1920) -> list[bytes]:
    """Render every PDF page; prefer PyMuPDF but support Poppler alone."""
    try:
        import fitz  # type: ignore
    except ImportError:
        fitz = None
    if fitz is not None:
        data = []
        with fitz.open(pdf) as doc:
            for page in doc:
                scale = width / page.rect.width
                pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale), alpha=False)
                data.append(pix.tobytes("png"))
        return data
    _find_executable("pdftoppm")
    with tempfile.TemporaryDirectory(prefix="subtree-png-") as tmp:
        stem = Path(tmp) / "page"
        _run(["pdftoppm", "-png", "-r", "120", str(pdf), str(stem)])
        files = sorted(stem.parent.glob("page-*.png"), key=lambda p: int(p.stem.split("-")[-1]))
        return [p.read_bytes() for p in files]


def _markdown_html(markdown: str) -> str:
    """Use optional Mistune; small safe fallback for truly dependency-free builds."""
    try:
        import mistune  # type: ignore
    except ImportError:
        # Preserve all narration even without an optional Markdown formatter.
        blocks = re.split(r"\n\s*\n", markdown.strip())
        return "\n".join("<p>" + html.escape(" ".join(b.splitlines())) + "</p>" for b in blocks)
    return mistune.create_markdown(escape=True)(markdown)


def find_video(scene: str) -> Path | None:
    directory = MEDIA / "videos"
    if not directory.exists():
        return None
    matches = [p for p in directory.rglob(scene + ".mp4") if p.is_file()]
    if not matches:
        return None
    return max(matches, key=lambda p: p.stat().st_mtime)


# This HTML is intentionally self-contained apart from optional chapter videos.
# Slide imagery is embedded; no CDN, web server, or internet access is required.
_PAGE_STYLE = r"""
:root { color-scheme: dark; --bg:#091321; --panel:#112438; --line:#30435a;
  --ink:#f3f6fc; --muted:#a5b7c9; --accent:#38d5c7; --amber:#ffc36b; }
* { box-sizing:border-box; }
html,body { height:100%; margin:0; }
body { background:var(--bg); color:var(--ink); font:15px/1.5 system-ui,Segoe UI,Arial,sans-serif; }
button,select,a { font:inherit; }
button,select { background:#182e44; color:var(--ink); border:1px solid #3c566f;
  border-radius:8px; padding:.44rem .7rem; cursor:pointer; }
button:hover,select:hover { border-color:var(--accent); }
button:disabled { opacity:.35; cursor:default; }
button:focus-visible,a:focus-visible,select:focus-visible { outline:3px solid var(--amber); outline-offset:2px; }
.top { min-height:64px; display:flex; align-items:center; gap:12px; padding:10px 20px;
  border-bottom:1px solid var(--line); flex-wrap:wrap; }
.brand { font-size:.98rem; font-weight:750; white-space:nowrap; }
.brand small { display:block; color:var(--muted); font-size:.7rem; font-weight:500; }
.top .space { flex:1; }
.controls { display:flex; align-items:center; gap:8px; flex-wrap:wrap; }
.controls button { min-width:40px; }
#chapter-picker { max-width:min(42vw,400px); }
#count { white-space:nowrap; color:var(--muted); font-variant-numeric:tabular-nums; }
.link { color:var(--accent); text-decoration:none; border:1px solid var(--line);
  border-radius:8px; padding:.43rem .7rem; }
.link:hover { text-decoration:underline; }
main { min-height:calc(100dvh - 68px); display:flex; align-items:center;
  justify-content:center; padding:clamp(10px,2vw,26px); gap:20px; }
.stage { flex:1; max-width:1500px; min-width:0; }
.scene { display:none; }
.scene.current { display:block; }
.stage-head { display:flex; gap:12px; align-items:baseline; justify-content:space-between;
  padding:0 0 9px; }
.stage-head h1 { font-size:clamp(16px,2.1vw,26px); margin:0; font-weight:650; }
.stage-head .track { color:var(--accent); font-size:.8rem; letter-spacing:.065em; text-transform:uppercase; }
.screen { width:100%; position:relative; aspect-ratio:16 / 9; background:#0b1525;
  overflow:hidden; box-shadow:0 12px 40px #0008; border:1px solid var(--line); border-radius:8px; }
.screen img, .screen video { position:absolute; inset:0; width:100%; height:100%; object-fit:contain; }
.screen video { display:none; background:#07101c; }
.screen.show-video video { display:block; }
.screen.show-video img { display:none; }
.scene-actions { display:flex; justify-content:space-between; align-items:center; gap:12px;
  margin-top:12px; color:var(--muted); }
.scene-actions .action-buttons { display:flex; gap:8px; }
.hint { font-size:.78rem; }
#narration { display:none; width:min(420px,33vw); flex:none; max-height:calc(100dvh - 130px);
  overflow:auto; padding:20px 24px; background:var(--panel); border:1px solid var(--line);
  border-radius:10px; box-shadow:0 5px 20px #0003; }
body.notes-open #narration { display:block; }
#narration h2 { margin:0 0 16px; font-size:1.15rem; }
#narration p { color:#d6e1ee; margin:0 0 1rem; }
#narration strong { color:#ffffff; }
#narration code { color:var(--amber); overflow-wrap:anywhere; }
#narration .narrative { overflow-wrap:anywhere; }
.progress { height:3px; background:#17293c; }
.progress div { width:0; height:100%; background:var(--accent); transition:width .22s; }
footer { text-align:center; font-size:.72rem; color:var(--muted); padding:4px 15px 12px; }
@media(max-width:1000px) { main { flex-direction:column; align-items:stretch; }
  body.notes-open #narration { display:block; width:100%; max-height:none; } }
@media(max-width:600px) { .top { padding:10px; } .brand { width:100%; }
  #chapter-picker { max-width:88vw; width:100%; } .hint { display:none; } }
@media print { .top,.scene-actions,#narration,footer,.progress { display:none !important; }
  body { background:#fff; } main,.stage { margin:0; padding:0; width:100%; max-width:none; }
  .scene { display:block !important; page-break-after:always; break-after:page; }
  .stage-head { display:none; } .screen { border:0; border-radius:0; box-shadow:none; }
  .screen img { display:block !important; } .screen video { display:none !important; }
  @page { size:13.333333in 7.5in; margin:0; } }
"""

_PAGE_SCRIPT = r"""
(function () {
'use strict';
const scenes = Array.from(document.querySelectorAll('.scene'));
const picker = document.getElementById('chapter-picker');
const count = document.getElementById('count');
const title = document.getElementById('notes-title');
const note = document.getElementById('notes-body');
const progress = document.getElementById('bar');
let current = 0;
function setMode(scene, videoOn) {
  const screen = scene.querySelector('.screen');
  const video = scene.querySelector('video');
  const videoButton = scene.querySelector('.toggle-video');
  const enabled = videoOn && Boolean(video);
  screen.classList.toggle('show-video', enabled);
  if (videoButton) videoButton.textContent = enabled ? 'Show slide' : 'Watch animation';
  if (!enabled && video) video.pause();
}
function jump(index, updateHash=true) {
  if (index < 0 || index >= scenes.length) return;
  const old = scenes[current];
  if (old) { const v = old.querySelector('video'); if (v) v.pause(); old.classList.remove('current'); }
  current = index;
  const scene = scenes[current]; scene.classList.add('current');
  setMode(scene, false);
  picker.value = String(current);
  count.textContent = `${current+1} / ${scenes.length}`;
  document.getElementById('prev').disabled = current === 0;
  document.getElementById('next').disabled = current === scenes.length - 1;
  title.textContent = scene.dataset.title;
  note.innerHTML = scene.querySelector('template').innerHTML;
  progress.style.width = `${100 * (current+1) / scenes.length}%`;
  if (updateHash) history.replaceState(null,'','#' + scene.dataset.scene);
}
document.getElementById('prev').addEventListener('click',()=>jump(current-1));
document.getElementById('next').addEventListener('click',()=>jump(current+1));
picker.addEventListener('change',()=>jump(Number(picker.value)));
document.getElementById('notes').addEventListener('click',()=>{
  const expanded = document.body.classList.toggle('notes-open');
  document.getElementById('notes').setAttribute('aria-pressed', String(expanded));
});
document.getElementById('full').addEventListener('click',()=>{
  const target = document.querySelector('.scene.current .screen');
  if (document.fullscreenElement) document.exitFullscreen();
  else if (target.requestFullscreen) target.requestFullscreen();
});
scenes.forEach(scene=>{
  const button = scene.querySelector('.toggle-video');
  if (button) button.addEventListener('click',()=>{
    const screen = scene.querySelector('.screen');
    const enable = !screen.classList.contains('show-video');
    setMode(scene, enable);
    if (enable) { const video = scene.querySelector('video'); video.play().catch(()=>{}); }
  });
});
document.addEventListener('keydown',e=>{
  if (e.altKey || e.ctrlKey || e.metaKey) return;
  if (['INPUT','TEXTAREA','SELECT','BUTTON'].includes(document.activeElement.tagName)) return;
  if (e.key==='ArrowRight' || e.key==='PageDown') { e.preventDefault(); jump(current+1); }
  if (e.key==='ArrowLeft' || e.key==='PageUp') { e.preventDefault(); jump(current-1); }
  if (e.key.toLowerCase()==='n') document.getElementById('notes').click();
  if (e.key.toLowerCase()==='f') document.getElementById('full').click();
});
window.addEventListener('hashchange',()=>{
  const id = decodeURIComponent(location.hash.slice(1));
  const idx = scenes.findIndex(s=>s.dataset.scene===id);
  if (idx>=0 && idx!==current) jump(idx,false);
});
const initial = scenes.findIndex(s=>s.dataset.scene===decodeURIComponent(location.hash.slice(1)));
jump(initial<0?0:initial,false);
})();
"""


def build_html(pdf: Path) -> Path:
    chapters = read_chapters()
    slides = _slide_pngs(pdf)
    if len(slides) != len(chapters):
        raise ValueError(f"PDF has {len(slides)} pages but storyboard has {len(chapters)} chapters")
    snippets = []
    options = []
    video_count = 0
    for index, (chapter, raw_png) in enumerate(zip(chapters, slides)):
        src = "data:image/png;base64," + base64.b64encode(raw_png).decode("ascii")
        video = find_video(chapter.scene)
        video_html = ""
        button = '<span class="hint">Static slide · no video rendered yet</span>'
        if video is not None:
            # HTML and generated videos normally live below presentations/media/.
            relative = video.relative_to(MEDIA).as_posix()
            video_src = quote(relative, safe="/-._~")
            video_html = f'<video controls playsinline preload="none" src="{html.escape(video_src)}"></video>'
            button = '<button class="toggle-video" type="button">Watch animation</button>'
            video_count += 1
        note_html = _markdown_html(chapter.narration)
        snippets.append(f'''<article class="scene" data-scene="{html.escape(chapter.scene)}" data-title="{html.escape(chapter.title, quote=True)}">
          <div class="stage-head"><h1>{html.escape(chapter.title)}</h1><span class="track">{html.escape(chapter.track)}</span></div>
          <div class="screen"><img src="{src}" alt="Slide {index+1}: {html.escape(chapter.title,quote=True)}" />{video_html}</div>
          <div class="scene-actions"><span>Chapter {index+1:02} · {html.escape(chapter.scene)}</span>
            <div class="action-buttons">{button}</div></div>
          <template>{note_html}</template>
        </article>''')
        options.append(f'<option value="{index}">{index+1:02}. {html.escape(chapter.title)}</option>')
    document = f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8" /><meta name="viewport" content="width=device-width,initial-scale=1" />
<title>Common Subtrees — Mathematical Presentation</title>
<meta name="description" content="Offline mathematical presentation of ordered tree contraction, weighted subtree matching, and distance-penalized embeddings." />
<style>{_PAGE_STYLE}</style></head><body>
<header class="top">
 <div class="brand">COMMON SUBTREES <small>Mathematical algorithms · Manim chapters</small></div>
 <div class="space"></div>
 <div class="controls">
  <button type="button" id="prev" aria-label="Previous chapter">‹</button>
  <select id="chapter-picker" aria-label="Select chapter">{''.join(options)}</select>
  <button type="button" id="next" aria-label="Next chapter">›</button>
  <span id="count" aria-live="polite"></span>
  <button type="button" id="notes" aria-pressed="false">Narration</button>
  <button type="button" id="full">Fullscreen</button>
  <a class="link" href="{PDF_NAME}">PDF</a>
 </div>
</header><div class="progress"><div id="bar"></div></div>
<main><div class="stage">{''.join(snippets)}</div>
<aside id="narration" aria-label="Chapter narration"><h2 id="notes-title"></h2><div id="notes-body" class="narrative"></div></aside>
</main><footer>Use ← / → to change chapters, N for narration, F for fullscreen. {video_count} animated chapters found; static slides always available.</footer>
<script>{_PAGE_SCRIPT}</script></body></html>'''
    dest = MEDIA / HTML_NAME
    dest.write_text(document, encoding="utf-8")
    print(f"Wrote {dest} ({len(chapters)} slides; {video_count} videos linked)")
    return dest


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--html", action="store_true", help="write an offline HTML viewer")
    parser.add_argument("--pdf", action="store_true", help="write 16:9 PDF slides")
    parser.add_argument("--rebuild-storyboard", action="store_true", help="force rebuilding the PPTX source")
    args = parser.parse_args(argv)
    if not args.html and not args.pdf:
        parser.error("Select --html and/or --pdf")
    # HTML uses static slide images from the same PDF that users can print.
    pdf = build_pdf(rebuild_storyboard=args.rebuild_storyboard)
    if args.html:
        build_html(pdf)


if __name__ == "__main__":
    main()
