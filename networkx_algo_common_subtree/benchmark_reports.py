"""Reporting helpers for common-subtree benchmark results.

The Rust benchmark target emits one machine-readable row per algorithm/case.
This module turns those rows into review artifacts: markdown for checked-in
reports, optional Rich tables for terminals, and structured JSON for downstream
analysis.
"""
from __future__ import annotations

from collections import defaultdict
import csv
from dataclasses import asdict, dataclass, field
import io
import json
from pathlib import Path
from typing import Iterable, TextIO

SCHEMA = "networkx_algo_common_subtree.pytorch_sized_benchmark_result.v1"


@dataclass(frozen=True)
class BenchmarkResult:
    """One benchmark result row for one algorithm on one case."""

    schema: str
    profile: str
    case: str
    algorithm: str
    left_nodes: int
    right_nodes: int
    median_seconds: float
    weight: float
    node_pairs: int
    left_match_ratio: float
    right_match_ratio: float
    skip_penalty: float | None = None
    warmup: int | None = None
    repeat: int | None = None
    sample_pairs: tuple[str, ...] = ()
    label_counts: tuple[tuple[str, int], ...] = ()
    description: str = ""

    @classmethod
    def from_mapping(cls, row: dict) -> "BenchmarkResult":
        """Build a result from JSON-style data with tolerant field parsing."""

        label_counts_raw = row.get("label_counts", ()) or ()
        label_counts: list[tuple[str, int]] = []
        if isinstance(label_counts_raw, str):
            for part in label_counts_raw.split("|"):
                part = part.strip()
                if not part:
                    continue
                name, _, count_text = part.partition(":")
                if count_text:
                    label_counts.append((name.strip(), int(count_text)))
        else:
            for item in label_counts_raw:
                if isinstance(item, dict):
                    label_counts.append((str(item["label"]), int(item["count"])))
                else:
                    label, count = item
                    label_counts.append((str(label), int(count)))

        sample_pairs_raw = row.get("sample_pairs", ()) or ()
        if isinstance(sample_pairs_raw, str):
            sample_pairs = tuple(part.strip() for part in sample_pairs_raw.split("|") if part.strip())
        else:
            sample_pairs = tuple(str(item) for item in sample_pairs_raw)

        skip_penalty_raw = row.get("skip_penalty", None)
        skip_penalty = None if skip_penalty_raw in (None, "", "null") else float(skip_penalty_raw)

        return cls(
            schema=str(row.get("schema", SCHEMA)),
            profile=str(row.get("profile", "")),
            case=str(row["case"]),
            algorithm=str(row["algorithm"]),
            left_nodes=int(row["left_nodes"]),
            right_nodes=int(row["right_nodes"]),
            median_seconds=float(row["median_seconds"]),
            weight=float(row["weight"]),
            node_pairs=int(row["node_pairs"]),
            left_match_ratio=float(row.get("left_match_ratio", int(row["node_pairs"]) / int(row["left_nodes"]))),
            right_match_ratio=float(row.get("right_match_ratio", int(row["node_pairs"]) / int(row["right_nodes"]))),
            skip_penalty=skip_penalty,
            warmup=_optional_int(row.get("warmup")),
            repeat=_optional_int(row.get("repeat")),
            sample_pairs=sample_pairs,
            label_counts=tuple(label_counts),
            description=str(row.get("description", "")),
        )

    def to_json_dict(self) -> dict:
        """Return a stable JSON-compatible representation."""

        data = asdict(self)
        data["sample_pairs"] = list(self.sample_pairs)
        data["label_counts"] = [
            {"label": label, "count": count} for label, count in self.label_counts
        ]
        return data


def _optional_int(value) -> int | None:
    if value in (None, "", "null"):
        return None
    return int(value)


def load_benchmark_results(path: str | Path) -> list[BenchmarkResult]:
    """Load benchmark rows from JSONL, JSON-list, or CSV."""

    text = Path(path).read_text()
    return parse_benchmark_results(text)


def parse_benchmark_results(text: str) -> list[BenchmarkResult]:
    """Parse benchmark rows from JSONL, JSON-list, or CSV text."""

    stripped = text.strip()
    if not stripped:
        return []
    first = stripped[0]
    if first == "[":
        payload = json.loads(stripped)
        return [BenchmarkResult.from_mapping(row) for row in payload]
    if first == "{":
        rows = [json.loads(line) for line in stripped.splitlines() if line.strip()]
        return [BenchmarkResult.from_mapping(row) for row in rows]

    reader = csv.DictReader(io.StringIO(stripped))
    return [BenchmarkResult.from_mapping(row) for row in reader]


def benchmark_results_json(rows: Iterable[BenchmarkResult], *, indent: int = 2) -> str:
    """Serialize result rows as a JSON array."""

    payload = [row.to_json_dict() for row in rows]
    return json.dumps(payload, indent=indent, sort_keys=True) + "\n"


def benchmark_results_jsonl(rows: Iterable[BenchmarkResult]) -> str:
    """Serialize result rows as newline-delimited JSON."""

    return "".join(json.dumps(row.to_json_dict(), sort_keys=True) + "\n" for row in rows)


def render_markdown_report(rows: Iterable[BenchmarkResult]) -> str:
    """Render a human-readable markdown report."""

    rows = list(rows)
    lines = [
        "# PyTorch-sized common-subtree benchmark results",
        "",
        "## Algorithm comparison",
        "",
    ]
    comparison_header = [
        "case",
        "size",
        "iso sec",
        "iso pairs",
        "embed sec",
        "embed pairs",
        "pair delta",
        "time ratio",
        "embed weight",
    ]
    comparison_rows = []
    for case, by_algorithm in _rows_by_case(rows):
        iso = by_algorithm.get("isomorphism")
        emb = by_algorithm.get("embedding")
        left_nodes = (iso or emb).left_nodes
        right_nodes = (iso or emb).right_nodes
        comparison_rows.append([
            case,
            f"{left_nodes}/{right_nodes}",
            _fmt_seconds(iso.median_seconds) if iso else "-",
            str(iso.node_pairs) if iso else "-",
            _fmt_seconds(emb.median_seconds) if emb else "-",
            str(emb.node_pairs) if emb else "-",
            _fmt_signed_int((emb.node_pairs if emb else 0) - (iso.node_pairs if iso else 0))
            if iso and emb else "-",
            _fmt_ratio((emb.median_seconds / iso.median_seconds) if iso and emb and iso.median_seconds else None),
            _fmt_weight(emb.weight) if emb else "-",
        ])
    lines.extend(_markdown_table(comparison_header, comparison_rows))

    lines.extend(["", "## Match detail", ""])
    detail_header = [
        "case",
        "algorithm",
        "weight",
        "pairs",
        "left %",
        "right %",
        "labels",
        "sample pairs",
    ]
    detail_rows = []
    for row in sorted(rows, key=lambda r: (r.case, r.algorithm)):
        detail_rows.append([
            row.case,
            row.algorithm,
            _fmt_weight(row.weight),
            str(row.node_pairs),
            _fmt_pct(row.left_match_ratio),
            _fmt_pct(row.right_match_ratio),
            _compact_label_counts(row.label_counts),
            _compact_sample_pairs(row.sample_pairs, max_items=2),
        ])
    lines.extend(_markdown_table(detail_header, detail_rows))
    lines.append("")
    return "\n".join(lines)


def print_rich_report(rows: Iterable[BenchmarkResult], *, file: TextIO | None = None) -> bool:
    """Print a Rich report if Rich is installed.

    Returns ``True`` when Rich handled the output and ``False`` when callers
    should fall back to markdown/plain rendering.
    """

    try:
        from rich.console import Console, Group
        from rich.table import Table
        from rich.panel import Panel
    except Exception:  # pragma: no cover - exercised when rich is absent
        return False

    rows = list(rows)
    console = Console(file=file, force_terminal=True if file is None else None)

    comparison = Table(title="PyTorch-sized common-subtree benchmark comparison", show_lines=False)
    comparison.add_column("Case", overflow="fold")
    comparison.add_column("Size", justify="right")
    comparison.add_column("Iso sec", justify="right")
    comparison.add_column("Iso pairs", justify="right")
    comparison.add_column("Embed sec", justify="right")
    comparison.add_column("Embed pairs", justify="right")
    comparison.add_column("Δ pairs", justify="right")
    comparison.add_column("Time ×", justify="right")

    for case, by_algorithm in _rows_by_case(rows):
        iso = by_algorithm.get("isomorphism")
        emb = by_algorithm.get("embedding")
        left_nodes = (iso or emb).left_nodes
        right_nodes = (iso or emb).right_nodes
        comparison.add_row(
            case,
            f"{left_nodes}/{right_nodes}",
            _fmt_seconds(iso.median_seconds) if iso else "-",
            str(iso.node_pairs) if iso else "-",
            _fmt_seconds(emb.median_seconds) if emb else "-",
            str(emb.node_pairs) if emb else "-",
            _fmt_signed_int((emb.node_pairs if emb else 0) - (iso.node_pairs if iso else 0))
            if iso and emb else "-",
            _fmt_ratio((emb.median_seconds / iso.median_seconds) if iso and emb and iso.median_seconds else None),
        )

    detail = Table(title="Representative match detail", show_lines=True)
    detail.add_column("Case", overflow="fold")
    detail.add_column("Algorithm")
    detail.add_column("Weight", justify="right")
    detail.add_column("Pairs", justify="right")
    detail.add_column("Left", justify="right")
    detail.add_column("Right", justify="right")
    detail.add_column("Top labels", overflow="fold")
    detail.add_column("Sample module pairs", overflow="fold")

    for row in sorted(rows, key=lambda r: (r.case, r.algorithm)):
        detail.add_row(
            row.case,
            row.algorithm,
            _fmt_weight(row.weight),
            str(row.node_pairs),
            _fmt_pct(row.left_match_ratio),
            _fmt_pct(row.right_match_ratio),
            _compact_label_counts(row.label_counts, max_items=5),
            _compact_sample_pairs(row.sample_pairs, max_items=3),
        )

    console.print(Panel(Group(comparison, detail), title="Common subtree benchmarks"))
    return True


def print_benchmark_report(
    rows: Iterable[BenchmarkResult],
    *,
    report_format: str = "rich",
    file: TextIO | None = None,
) -> None:
    """Print benchmark rows in ``rich``, ``markdown``, ``json``, or ``jsonl`` format."""

    rows = list(rows)
    if report_format == "rich":
        if print_rich_report(rows, file=file):
            return
        report_format = "markdown"

    output = file if file is not None else None
    if report_format == "markdown":
        text = render_markdown_report(rows)
    elif report_format == "json":
        text = benchmark_results_json(rows)
    elif report_format == "jsonl":
        text = benchmark_results_jsonl(rows)
    else:
        raise KeyError(f"unknown report format: {report_format!r}")

    if output is None:
        print(text, end="")
    else:
        output.write(text)


def _rows_by_case(rows: Iterable[BenchmarkResult]):
    grouped = defaultdict(dict)
    for row in rows:
        grouped[row.case][row.algorithm] = row
    for case in sorted(grouped):
        yield case, grouped[case]


def _markdown_table(header: list[str], rows: list[list[str]]) -> list[str]:
    escaped_header = [_escape_md(cell) for cell in header]
    out = ["| " + " | ".join(escaped_header) + " |"]
    out.append("| " + " | ".join(["---"] * len(header)) + " |")
    for row in rows:
        out.append("| " + " | ".join(_escape_md(str(cell)) for cell in row) + " |")
    return out


def _escape_md(text: str) -> str:
    return text.replace("|", "\\|").replace("\n", "<br>")


def _fmt_seconds(value: float) -> str:
    if value < 0.001:
        return f"{value * 1_000_000:.1f} µs"
    if value < 1.0:
        return f"{value * 1000:.2f} ms"
    return f"{value:.3f} s"


def _fmt_weight(value: float) -> str:
    if abs(value - round(value)) < 1e-9:
        return str(int(round(value)))
    return f"{value:.3f}"


def _fmt_pct(value: float) -> str:
    return f"{100.0 * value:.1f}%"


def _fmt_signed_int(value: int) -> str:
    return f"{value:+d}"


def _fmt_ratio(value: float | None) -> str:
    if value is None:
        return "-"
    return f"{value:.2f}×"


def _compact_label_counts(label_counts: Iterable[tuple[str, int]], *, max_items: int = 6) -> str:
    items = sorted(label_counts, key=lambda item: (-item[1], item[0]))
    shown = [f"{name}:{count}" for name, count in items[:max_items]]
    if len(items) > max_items:
        shown.append("...")
    return ", ".join(shown)


def _compact_sample_pairs(sample_pairs: Iterable[str], *, max_items: int = 3) -> str:
    items = list(sample_pairs)
    shown = items[:max_items]
    if len(items) > max_items:
        shown.append("...")
    return "; ".join(shown)


__all__ = [
    "BenchmarkResult",
    "SCHEMA",
    "benchmark_results_json",
    "benchmark_results_jsonl",
    "load_benchmark_results",
    "parse_benchmark_results",
    "print_benchmark_report",
    "print_rich_report",
    "render_markdown_report",
]
