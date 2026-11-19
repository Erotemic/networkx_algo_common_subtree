"""Authoritative speaker notes from the mathematical storyboard.

This initial integration gives each chapter a readable opening note.  Future
slide-by-slide narration should split those sections into explicit beats,
like the DKPS lecture transcripts, rather than inventing timing heuristics.
"""
from __future__ import annotations

from functools import lru_cache
from pathlib import Path
import re

STORYBOARD = Path(__file__).with_name("STORYBOARD.md")
HEADING = re.compile(r"^## \d+\. ([A-Za-z][A-Za-z0-9]*)\s+.*$", re.MULTILINE)


@lru_cache(maxsize=1)
def chapter_notes() -> dict[str, str]:
    body = STORYBOARD.read_text(encoding="utf-8")
    headings = list(HEADING.finditer(body))
    chapters = {}
    for i, match in enumerate(headings):
        tail = headings[i + 1].start() if i + 1 < len(headings) else len(body)
        text = body[match.end():tail].strip()
        # Presenter notes need meaning, not Markdown heading syntax.
        text = re.sub(r"\*\*(.+?)\*\*", r"\1", text)
        text = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", r"\1", text)
        chapters[match.group(1)] = text
    return chapters


def notes_for(scene_name: str) -> str:
    try:
        return chapter_notes()[scene_name]
    except KeyError as exc:
        raise KeyError(f"Missing storyboard narration for {scene_name}") from exc
