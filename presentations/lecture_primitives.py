"""Readable, bounded content building blocks for the three standalone talks.

All geometry stays within the 16:9 Manim frame.  Every content reveal is
initiated by the caller after an explicit `beat()` narration boundary.
"""
from __future__ import annotations

from manim import FadeIn, Write, VGroup, DOWN, LEFT, RIGHT

from scenes import MathTex
from visuals import FG, MUTED, PANEL_BORDER, TEAL, panel, t


def formula(tex: str, *, y: float = 1.2, scale: float = 0.9, color: str = FG):
    mob = MathTex(tex, color=color).scale(scale)
    if mob.width > 11.8:
        mob.scale_to_fit_width(11.8)
    return mob.move_to([0, y, 0])


def strip(title: str, detail: str, *, y: float, accent: str = TEAL,
          width: float = 11.9, height: float = .81):
    bg = panel(width, height).move_to([0, y, 0])
    lhs = t(title, 19, accent)
    if lhs.width > 3.5:
        lhs.scale_to_fit_width(3.5)
    lhs.move_to([-4.05, y, 0])
    rhs = t(detail, 20, FG)
    if rhs.width > 7.30:
        rhs.scale_to_fit_width(7.30)
    rhs.move_to([1.58, y, 0])
    return VGroup(bg, lhs, rhs)


def show_rows(scene, rows, *, start: float = 1.60, step: float = .95):
    """Rows are (label, detail, color, spoken_note), one click per row."""
    for i, (label, detail, color, note) in enumerate(rows):
        if i:
            scene.beat(notes=note)
        line = strip(label, detail, y=start-i*step, accent=color)
        scene.play(FadeIn(line), run_time=.55)


def side_formula(tex: str, *, x: float, y: float, scale: float = .75, color: str = FG,
                 max_width: float = 5.75):
    mob = MathTex(tex, color=color).scale(scale)
    if mob.width > max_width:
        mob.scale_to_fit_width(max_width)
    return mob.move_to([x,y,0])


def center_text(text: str, *, y: float, size: int = 22, color: str = MUTED,
                width: float = 11.80):
    mob = t(text, size, color)
    if mob.width > width:
        mob.scale_to_fit_width(width)
    return mob.move_to([0, y, 0])
