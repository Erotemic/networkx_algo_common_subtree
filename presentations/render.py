#!/usr/bin/env python3
"""Render one scene or the full mathematical presentation with Manim.

Examples:
    python3 presentations/render.py --check
    python3 presentations/render.py --list
    python3 presentations/render.py --scene OrderedRecurrence --quality l
    python3 presentations/render.py --all --quality h --stitch

Optional interactive slides: manim-slides render presentations/scenes.py SCENE_NAME
"""
from __future__ import annotations

import argparse
import importlib.util
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCENES = (
    "AllProblems", "OrderedContraction", "BalancedWords",
    "DeletionIsContraction", "OrderedRecurrence", "CorrectnessAndComplexity",
    "AffinityExtensions", "WeightedUnorderedMatching",
    "SparseMatchingOptimization", "TopologicalDistancePenalties",
    "MappedAndSkippedStates", "ProofBoundary", "ApplicationExperiment", "PaperContribution",
)


def execute(args: list[str]) -> None:
    print("+", " ".join(args), flush=True)
    subprocess.run(args, check=True, cwd=HERE.parent)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="list scene class names")
    parser.add_argument("--check", action="store_true", help="check examples, tools, and MathTex when Manim is installed")
    parser.add_argument("--check-tex", action="store_true", help="compile all scene formulas using Manim and its LaTeX template")
    parser.add_argument("--scene", choices=SCENES)
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--quality", choices=("l", "m", "h", "k"), default="m")
    parser.add_argument("--stitch", action="store_true", help="combine individual scene videos into one MP4")
    parser.add_argument("--dry-run", action="store_true", help="print render commands")
    options = parser.parse_args()

    if options.list:
        print("\n".join(SCENES))
        return
    if options.check_tex:
        if importlib.util.find_spec("manim") is None:
            parser.error("Manim is required for --check-tex")
        sys.path.insert(0, str(HERE))
        from tex_preflight import check_manim_tex
        check_manim_tex(HERE / "scenes.py")
        return
    if options.check:
        print("manim available:", importlib.util.find_spec("manim") is not None)
        print("manim-slides available:", importlib.util.find_spec("manim_slides") is not None)
        print("ffmpeg available:", shutil.which("ffmpeg") is not None)
        execute([sys.executable, "-m", "unittest", "discover", "-s", "presentations/tests", "-v"])
        if importlib.util.find_spec("manim") is not None:
            sys.path.insert(0, str(HERE))
            from tex_preflight import check_manim_tex
            check_manim_tex(HERE / "scenes.py")
        else:
            print("MathTex check skipped: Manim is not installed")
        return
    names = SCENES if options.all else ((options.scene,) if options.scene else ())
    if not names:
        parser.error("choose --scene NAME, --all, --list or --check")

    # For reliable stitching, all scenes must use exactly the same frame rate/resolution.
    video_dir = HERE / "media" / "videos" / "scenes" / f"{options.quality}"
    if not options.dry_run and importlib.util.find_spec("manim") is None:
        parser.error("Manim is not installed: pip install -r presentations/requirements.txt")
    for name in names:
        command = [sys.executable, "-m", "manim", f"-q{options.quality}", "--format", "mp4",
                   "--media_dir", str(HERE / "media"), "-o", f"{name}.mp4",
                   str(HERE / "scenes.py"), name]
        if options.dry_run:
            print("+", " ".join(command))
        else:
            execute(command)
    if options.stitch:
        if not options.all:
            parser.error("--stitch requires --all")
        if options.dry_run:
            print("+ ffmpeg concat (requires the scene files to exist)")
            return
        # Manim's output paths include quality/resolution names and may vary by version.
        # Locate videos by name rather than guessing the media subfolder structure.
        found = []
        for name in names:
            matches = sorted((HERE / "media").rglob(name + ".mp4"), key=lambda p: p.stat().st_mtime)
            if not matches:
                raise FileNotFoundError(f"No rendered video for {name}")
            found.append(matches[-1])
        # Write a concat playlist; re-encode to avoid timebase discontinuities.
        manifest = HERE / "media" / "lecture-concat.txt"
        manifest.write_text("".join("file '" + str(path).replace("'", "'\\''") + "'\n" for path in found))
        output = HERE / "media" / "common-subtree-mathematics.mp4"
        execute(["ffmpeg", "-y", "-f", "concat", "-safe", "0", "-i", str(manifest),
                 "-c:v", "libx264", "-pix_fmt", "yuv420p", "-crf", "18",
                 "-c:a", "aac", str(output)])
        print("Wrote", output)


if __name__ == "__main__":
    main()
