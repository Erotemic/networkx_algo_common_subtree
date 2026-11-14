"""Validate the presentation pipeline without requiring Manim to be installed."""
from __future__ import annotations

import ast
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
spec = importlib.util.spec_from_file_location("subtree_presentation_render", HERE / "render.py")
render = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(render)

from narration import chapter_notes  # noqa: E402


class NativeExportCommands(unittest.TestCase):
    def test_scene_registry_and_notes(self):
        self.assertEqual(len(render.SCENES), 14)
        self.assertEqual(len(set(render.SCENES)), 14)
        self.assertEqual(set(render.SCENES), set(chapter_notes()))
        for scene in render.SCENES:
            self.assertIn("Question:", chapter_notes()[scene])

    def test_dkps_style_render_command(self):
        cmd = render.native_slide_render_command("OrderedRecurrence", "h", 30)
        self.assertEqual(cmd[:4], [sys.executable, "-m", "manim_slides", "render"])
        self.assertIn("--quality=h", cmd)
        self.assertIn("--fps=30", cmd)
        self.assertEqual(cmd[-2:], ["scenes.py", "OrderedRecurrence"])

    def test_native_html_convert(self):
        cmd = render.native_slide_export_command(render.SCENES, "html")
        self.assertEqual(cmd[:4], [sys.executable, "-m", "manim_slides", "convert"])
        self.assertNotIn("--one-file", cmd)
        self.assertIn("--folder", cmd)
        self.assertIn(render.SLIDES_FOLDER, cmd)
        self.assertIn("--to", cmd)
        self.assertEqual(cmd[cmd.index("--to") + 1], "html")
        self.assertNotIn("--offline", cmd)
        self.assertIn("-cslide_number=true", cmd)
        self.assertIn("-ccontrols=false", cmd)
        self.assertIn("-cprogress=false", cmd)
        self.assertTrue(any(x.endswith("common-subtree-mathematics.html") for x in cmd))
        self.assertTrue(all(scene in cmd for scene in render.SCENES))

    def test_offline_and_one_file_require_distinct_export_modes(self):
        offline = render.native_slide_export_command(render.SCENES, "html", offline=True)
        self.assertIn("--offline", offline)
        self.assertNotIn("--one-file", offline)
        embedded = render.native_slide_export_command(render.SCENES, "html", one_file=True)
        self.assertIn("--one-file", embedded)
        self.assertNotIn("--offline", embedded)
        with self.assertRaisesRegex(ValueError, "combine"):
            render.native_slide_export_command(render.SCENES, "html", offline=True, one_file=True)

    def test_exposed_javascript_is_refused(self):
        valid = ('<!doctype html><html><body><div class="reveal"></div>'
                 '<script>function safe(){return 1}</script></body></html>')
        render.verify_native_html_document(valid)
        broken = ('<!doctype html><html><body><div class="reveal"></div>'
                  + ';function t(){return{async:!1,' + 'function x(){}'*500
                  + '</body></html>')
        with self.assertRaisesRegex(ValueError, "JavaScript rendered as page text"):
            render.verify_native_html_document(broken)

    def test_click_injection_uses_terminal_body_not_js_literal(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'slide.html'
            path.write_text('<html><body><div class="reveal"></div>'
                            '<script>var html = "</body>"; Reveal.initialize({})</script>'
                            '</body></html>')
            render.make_html_presentation_bare(path)
            result = path.read_text()
            self.assertIn('var html = "</body>";', result)
            self.assertEqual(result.count('id="subtree-fullscreen-click-advance"'), 1)
            self.assertTrue(result.endswith('</body></html>'))

    def test_pdf_uses_same_fragments(self):
        cmd = render.native_slide_export_command(render.SCENES, "pdf")
        self.assertIn(render.SLIDES_FOLDER, cmd)
        self.assertEqual(cmd[cmd.index("--to") + 1], "pdf")
        self.assertNotIn("--one-file", cmd)
        self.assertTrue(cmd[-1].endswith("common-subtree-mathematics.pdf"))
        self.assertTrue(all(scene in cmd for scene in render.SCENES))

    def test_fullscreen_click_advance_is_not_a_second_viewer(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "native.html"
            path.write_text('<html><body><div class="reveal"><div class="slides"></div></div>'
                            '<script>Reveal.initialize({});</script></body></html>')
            render.make_html_presentation_bare(path)
            result = path.read_text()
            self.assertIn("Reveal.next();", result)
            self.assertIn("subtree-fullscreen-click-advance", result)
            self.assertIn(".reveal .controls", result)
            self.assertIn(".reveal .slide-number", result)
            self.assertNotIn(".reveal .progress, .reveal .slide-number", result)
            self.assertNotIn("<iframe", result)
            self.assertEqual(result.count('id="subtree-fullscreen-click-advance"'), 1)
            render.make_html_presentation_bare(path)
            self.assertEqual(result, path.read_text())

    def test_native_pdf_receives_individual_page_numbers(self):
        try:
            import fitz
        except ImportError:
            self.skipTest("PyMuPDF not installed")
        with tempfile.TemporaryDirectory() as tmp:
            pdf = Path(tmp) / "native.pdf"
            with fitz.open() as doc:
                for _ in range(3):
                    doc.new_page(width=960, height=540)
                doc.save(pdf)
            render.number_native_pdf_pages(pdf)
            with fitz.open(pdf) as doc:
                self.assertEqual(len(doc), 3)
                for i, page in enumerate(doc, 1):
                    self.assertIn(f"{i} / 3", page.get_text())

    def test_classic_export_can_run_independently(self):
        import subprocess
        cmd = [sys.executable, str(HERE / "render.py"), "--classic-html", "--dry-run"]
        result = subprocess.run(cmd, text=True, capture_output=True, check=True)
        self.assertIn("export.py --html", result.stdout)
        self.assertNotIn("manim_slides", result.stdout)
        self.assertIn("--classic-html", subprocess.run(
            [sys.executable, str(HERE / "render.py"), "--help"],
            capture_output=True, text=True, check=True).stdout)

    def test_heading_and_card_text_are_constrained(self):
        scenes = (HERE / "scenes.py").read_text()
        visuals = (HERE / "visuals.py").read_text()
        self.assertIn('heading.scale_to_fit_width(12.20)', scenes)
        self.assertIn('heading.get_right()[0] > 6.41', scenes)
        self.assertIn('Text extends outside slide', scenes)
        self.assertIn('section.get_bottom()[1] <= line.get_y()', scenes)
        self.assertIn('item.scale_to_fit_width(width - .35)', visuals)

    def test_bad_export_and_bad_scene(self):
        with self.assertRaises(ValueError):
            render.native_slide_export_command(render.SCENES, "pptx")
        with self.assertRaises(ValueError):
            render.native_slide_render_command("NotAScene", "h")

    def test_missing_and_empty_metadata_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            with patch.object(render, "HERE", Path(tmp)):
                with self.assertRaises(FileNotFoundError):
                    render.verify_slide_metadata(("OrderedContraction",))
                folder = Path(tmp) / render.SLIDES_FOLDER
                folder.mkdir()
                (folder / "OrderedContraction.json").write_text(json.dumps({"slides": []}))
                with self.assertRaises(ValueError):
                    render.verify_slide_metadata(("OrderedContraction",))
                (folder / "OrderedContraction.json").write_text(json.dumps({"slides": [{"file": "clip.mp4"}]}))
                render.verify_slide_metadata(("OrderedContraction",))

    def test_scene_breaks_begin_before_animation_not_after(self):
        module = ast.parse((HERE / "scenes.py").read_text())
        klass = next(n for n in module.body if isinstance(n, ast.ClassDef) and n.name == "MathPresentation")
        self.assertEqual(klass.bases[0].id, "Slide")
        setup = next(n for n in klass.body if isinstance(n, ast.FunctionDef) and n.name == "setup_page")
        self.assertTrue(any(isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                            and n.func.attr == "next_slide" for n in ast.walk(setup)))
        for chapter in module.body:
            if not isinstance(chapter, ast.ClassDef) or chapter.name == "MathPresentation":
                continue
            constructs = [n for n in chapter.body if isinstance(n, ast.FunctionDef) and n.name == "construct"]
            if not constructs:
                continue
            last = constructs[0].body[-1]
            self.assertIsInstance(last, ast.Expr)
            self.assertIsInstance(last.value, ast.Call)
            self.assertEqual(last.value.func.attr, "finish", chapter.name)


if __name__ == "__main__":
    unittest.main()
