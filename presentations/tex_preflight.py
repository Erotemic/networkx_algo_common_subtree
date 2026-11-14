"""Compile the Manim lecture's mathematical expressions before video rendering.

The expression inventory is extracted from scene source so new MathTex formulas
are checked automatically.  The real Manim constructor and its actual TeX
configuration are used, which catches problems that syntax-only checks miss.
"""
from __future__ import annotations

import ast
from pathlib import Path


def scene_tex_candidates(source: Path) -> list[tuple[int, str]]:
    """Discover inline scene mathematics, including loop-provided formulas."""
    module = ast.parse(source.read_text(encoding="utf8"), filename=str(source))
    found: dict[str, int] = {}
    for class_def in module.body:
        if not isinstance(class_def, ast.ClassDef):
            continue
        for method in class_def.body:
            if not isinstance(method, (ast.FunctionDef, ast.AsyncFunctionDef)) or method.name != "construct":
                continue
            for expr in ast.walk(method):
                if isinstance(expr, ast.Constant) and isinstance(expr.value, str):
                    value = expr.value
                    # String constants containing TeX commands include formulas
                    # stored in tuples and evaluated later inside a loop.
                    if "\\" in value and "\n" not in value:
                        found.setdefault(value, expr.lineno)
                if (isinstance(expr, ast.Call) and isinstance(expr.func, ast.Name)
                        and expr.func.id == "MathTex"):
                    for arg in expr.args:
                        if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                            if "\n" not in arg.value:
                                found.setdefault(arg.value, arg.lineno)
    # A few formulas are generated from variables at runtime; their simplest
    # representative values should also be checked.
    for dynamic_example in ("0", "1", "M(u,v)", "S(u,v)", "8 + 7 = 15"):
        found.setdefault(dynamic_example, 0)
    return sorted(((line, expression) for expression, line in found.items()),
                  key=lambda pair: (pair[0], pair[1]))


def check_manim_tex(source: Path) -> int:
    """Return the number of equations successfully compiled by Manim."""
    # Imported here so scene_tex_candidates can also run without Manim.
    from scenes import MathTex
    candidates = scene_tex_candidates(source)
    for index, (line, expression) in enumerate(candidates, 1):
        try:
            MathTex(expression)
        except Exception as exc:
            raise RuntimeError(
                f"Manim MathTex preflight failed at {source.name}:{line} "
                f"({index}/{len(candidates)}): {expression!r}"
            ) from exc
    print(f"Compiled {len(candidates)} mathematical expressions with Manim's TeX template.")
    return len(candidates)
