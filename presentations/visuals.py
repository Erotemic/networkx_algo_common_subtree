"""Reusable Manim graphics for the common-subtree mathematical lectures."""
from __future__ import annotations

from manim import (
    Circle, Line, RoundedRectangle, Text, VGroup,
    UP, WHITE, config,
)

BG = "#0B1525"
PANEL = "#14243A"
PANEL_BORDER = "#2E4D68"
FG = "#F4F6FB"
MUTED = "#9DB3C8"
TEAL = "#35D5C5"
AMBER = "#FFC36B"
ROSE = "#FF758B"
BLUE = "#68A9FF"

config.background_color = BG


def t(text: str, size: int = 30, color: str = FG, **kwargs) -> Text:
    return Text(text, font="DejaVu Sans", font_size=size, color=color, **kwargs)


def panel(width: float, height: float) -> RoundedRectangle:
    return RoundedRectangle(
        width=width, height=height, corner_radius=0.16,
        fill_color=PANEL, fill_opacity=1, stroke_color=PANEL_BORDER, stroke_width=1.7,
    )


def card(title: str, subtitle: str, color: str, width=3.8, height=2.4) -> VGroup:
    rect = panel(width, height)
    header = t(title, 30, color)
    body = t(subtitle, 19, MUTED, line_spacing=1.05)
    for item in (header, body):
        if item.width > width - .35:
            item.scale_to_fit_width(width - .35)
    header.move_to(rect.get_center() + UP * .48)
    body.move_to(rect.get_center() - UP * .30)
    return VGroup(rect, header, body)


def tree_drawing(tree, anchor=(-3.2, 0.3), width=4.0, level_gap=1.05,
                 radius=.26, highlights=(), dim=()):
    """Render an arbitrary-arity ordered rooted tree with stable path-based IDs.

    Returns (VGroup, positions) where positions maps tuple child paths to 3-vectors.
    This is intentionally a presentation primitive; the oracle lives separately.
    """
    raw = {}
    nxt = [0]

    def assign(item, path, depth):
        if not item.children:
            x = float(nxt[0]); nxt[0] += 1
        else:
            xs = [assign(child, path + (i,), depth + 1)
                  for i, child in enumerate(item.children)]
            x = (xs[0] + xs[-1]) / 2
        raw[path] = (x, depth, item.label)
        return x

    assign(tree, (), 0)
    spread = max(1, nxt[0] - 1)
    scale = min(width / spread, 1.35)
    minx = min(q[0] for q in raw.values())
    maxx = max(q[0] for q in raw.values())
    origin_x, origin_y = anchor
    points = {
        path: [origin_x + (x - (minx + maxx)/2)*scale,
               origin_y - depth*level_gap, 0]
        for path, (x, depth, _) in raw.items()
    }
    edges = VGroup()
    vertices = VGroup()
    highlights = set(highlights)
    dim = set(dim)
    for path in sorted(raw, key=lambda p: (len(p), p)):
        if path:
            col = PANEL_BORDER if path in dim else (TEAL if path in highlights else MUTED)
            edges.add(Line(points[path[:-1]], points[path], color=col, stroke_width=5))
    for path in sorted(raw, key=lambda p: (len(p), p)):
        col = PANEL_BORDER if path in dim else (TEAL if path in highlights else BLUE)
        circ = Circle(radius=radius, color=col, stroke_width=3, fill_color=BG,
                      fill_opacity=1).move_to(points[path])
        label = t(raw[path][2], 18, FG if path not in dim else MUTED).move_to(points[path])
        vertices.add(VGroup(circ, label))
    return VGroup(edges, vertices), points


def weight_matrix(weights, selected=(), x=0, y=0, size=.78):
    """Small matrix with selected cells highlighted by exact row/column index."""
    selected = set(selected)
    result = VGroup()
    for r, row in enumerate(weights):
        for c, value in enumerate(row):
            box = RoundedRectangle(
                width=size*1.12, height=size, corner_radius=.08,
                fill_color=TEAL if (r, c) in selected else PANEL,
                fill_opacity=.22 if (r, c) in selected else 1,
                stroke_color=TEAL if (r, c) in selected else PANEL_BORDER,
                stroke_width=3 if (r, c) in selected else 1,
            ).move_to([x + (c-(len(row)-1)/2)*(size*1.18), y-r*(size*1.12), 0])
            label = t("×" if value is None else str(value), 26, FG).move_to(box)
            result.add(VGroup(box, label))
    return result
