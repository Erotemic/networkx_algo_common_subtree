"""Deck structure and build contracts; these checks do not require Manim."""
from __future__ import annotations

import ast
from pathlib import Path
import subprocess
import sys
import unittest

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
from deck import DECKS, MATHEMATICS


class ThreeDeckTests(unittest.TestCase):
    def test_three_independent_standalone_decks(self):
        for name in ('lozano', 'droschinsky', 'formalization'):
            deck = DECKS[name]
            self.assertGreaterEqual(len(deck.scenes), 12)
            self.assertEqual(len(deck.scenes), len(set(deck.scenes)))
            self.assertNotEqual(deck.slug, MATHEMATICS.slug)
            self.assertTrue(deck.slug.isascii())
            for scene in deck.scenes:
                source = HERE / deck.module_for(scene)
                self.assertTrue(source.exists())
                tree = ast.parse(source.read_text())
                self.assertIn(scene, [node.name for node in tree.body if isinstance(node, ast.ClassDef)])
        self.assertEqual(len({DECKS[x].slug for x in ('lozano','droschinsky','formalization')}), 3)

    def test_all_scene_modules_provide_narrated_click_builds(self):
        for file in ('lozano_scenes.py','droschinsky_scenes.py','formalization_scenes.py'):
            source = (HERE / file).read_text()
            tree = ast.parse(source)
            classes = [node for node in tree.body if isinstance(node, ast.ClassDef)]
            self.assertGreaterEqual(len(classes), 7)
            for cls in classes:
                self.assertTrue(any(isinstance(child,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='intro_notes' for t in child.targets) for child in cls.body), cls.name)
                self.assertTrue(any(isinstance(child,ast.FunctionDef) and child.name=='construct' for child in cls.body),cls.name)
                self.assertTrue('self.beat(' in ast.get_source_segment(source,cls) or 'show_rows(self,' in ast.get_source_segment(source,cls))
                self.assertIn('self.finish()',ast.get_source_segment(source,cls))

    def test_dry_run_uses_distinct_slides_folders_and_sources(self):
        for key, first_file in (
            ('lozano','lozano_scenes.py'),
            ('droschinsky','droschinsky_scenes.py'),
            ('formalization','formalization_scenes.py'),
        ):
            result = subprocess.run([sys.executable, str(HERE / 'render.py'),
                                     '--deck',key,'--html','--pdf','--dry-run','-q','l'],
                                    cwd=HERE,capture_output=True,text=True,check=True)
            self.assertIn(first_file,result.stdout)
            self.assertIn(DECKS[key].slug + '.html',result.stdout)
            self.assertIn(DECKS[key].slug + '.pdf',result.stdout)
            self.assertIn('slides-'+DECKS[key].slug,result.stdout)
            self.assertIn('-cslide_number=true',result.stdout)
            self.assertIn('-ccontrols=false',result.stdout)
            self.assertNotIn('storyboard_preview.js',result.stdout)

    def test_standalone_classic_not_conflated_with_new_decks(self):
        proc = subprocess.run([sys.executable,str(HERE/'render.py'),'--deck','lozano',
                               '--classic-html','--dry-run'],cwd=HERE,capture_output=True,text=True)
        self.assertNotEqual(proc.returncode,0)
        self.assertIn('only for the original mathematics deck',proc.stderr)

    def test_original_deck_preserved(self):
        proc = subprocess.run([sys.executable,str(HERE/'render.py'),'--deck','mathematics',
                               '--list'],cwd=HERE,capture_output=True,text=True,check=True)
        self.assertEqual(proc.stdout.splitlines(),list(MATHEMATICS.scenes))


if __name__ == '__main__':
    unittest.main()
