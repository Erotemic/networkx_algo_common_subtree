"""Smoke checks for offline HTML and PDF presentation integration."""
import sys
import tempfile
from pathlib import Path
from unittest import TestCase, mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import export  # noqa: E402
import render  # noqa: E402


class PresentationExportTests(TestCase):
    def test_chapter_order_matches_manim_and_storyboard(self):
        chapters = export.read_chapters()
        self.assertEqual(len(chapters), 14)
        self.assertEqual(tuple(ch.scene for ch in chapters), render.SCENES)
        self.assertEqual(tuple(ch.scene for ch in chapters), export.CHAPTER_SCENES)
        self.assertTrue(all(ch.narration and ch.title for ch in chapters))
        self.assertIn('edge contraction', chapters[1].narration)

    def test_offline_html_embeds_images_and_links_only_existing_videos(self):
        with tempfile.TemporaryDirectory() as d:
            media = Path(d)
            fake_video = media / 'videos' / '1080p' / 'AllProblems.mp4'
            fake_video.parent.mkdir(parents=True)
            fake_video.write_bytes(b'fake video; only path discovery matters')
            png = b'\x89PNG\r\n\x1a\n'  # HTML embeds the bytes; no image decoder needed.
            with mock.patch.object(export, 'MEDIA', media), mock.patch.object(
                export, '_slide_pngs', return_value=[png] * 14
            ):
                html_file = export.build_html(media / export.PDF_NAME)
            content = html_file.read_text(encoding='utf8')
            self.assertEqual(content.count('<article class="scene"'), 14)
            self.assertEqual(content.count('class="toggle-video"'), 1)
            self.assertIn('videos/1080p/AllProblems.mp4', content)
            self.assertIn('data:image/png;base64,', content)
            self.assertIn('id="chapter-picker"', content)
            self.assertIn('id="notes-body"', content)
            self.assertIn('href="common-subtree-mathematics.pdf"', content)
            self.assertNotIn('src="https://', content)

    def test_html_fails_if_pdf_slides_do_not_match_chapters(self):
        with tempfile.TemporaryDirectory() as d, mock.patch.object(export, 'MEDIA', Path(d)):
            with mock.patch.object(export, '_slide_pngs', return_value=[b'a'] * 13):
                with self.assertRaisesRegex(ValueError, '13 pages.*14 chapters'):
                    export.build_html(Path(d) / 'dummy.pdf')
