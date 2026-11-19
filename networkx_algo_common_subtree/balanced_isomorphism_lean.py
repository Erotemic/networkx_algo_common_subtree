"""Exact rational ordered isomorphism through the compiled, proved Lean solver.

Python token/graph conversion and JSON/process transport are tested boundaries.
The executable calls the proved memoized Lean definition directly. This module
never substitutes a different solver when the native executable is unavailable.
"""
from fractions import Fraction
from numbers import Rational
from pathlib import Path
import json
import operator
import os
import subprocess
import atexit
import threading
from typing import TextIO, cast


_worker = None
_worker_owner = os.getpid()
_worker_path = None
_worker_lock = threading.RLock()


def _stop_worker():
    global _worker
    if _worker is not None and _worker_owner == os.getpid():
        process, _worker = _worker, None
        try:
            cast(TextIO, process.stdin).close()
            process.wait(timeout=1)
        except (OSError, subprocess.TimeoutExpired):
            process.kill()
            process.wait()
        finally:
            cast(TextIO, process.stdout).close()
            cast(TextIO, process.stderr).close()


def _after_fork():
    global _worker, _worker_lock, _worker_owner, _worker_path
    if _worker is not None:
        # Close only this child's duplicate descriptors, never signal its parent.
        for stream in (_worker.stdin, _worker.stdout, _worker.stderr):
            cast(TextIO, stream).close()
    _worker = None
    _worker_path = None
    _worker_owner = os.getpid()
    _worker_lock = threading.RLock()


atexit.register(_stop_worker)
if hasattr(os, "register_at_fork"):
    os.register_at_fork(before=lambda: _worker_lock.acquire(),
                        after_in_parent=lambda: _worker_lock.release(),
                        after_in_child=_after_fork)


def _request(executable, request):
    """Reuse one serialized native worker; every request gets a fresh DP cache."""
    global _worker, _worker_owner, _worker_path
    with _worker_lock:
        if _worker is None or _worker_path != executable or _worker.poll() is not None:
            _stop_worker()
            _worker = subprocess.Popen([str(executable)], stdin=subprocess.PIPE,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       text=True, bufsize=1)
            _worker_owner, _worker_path = os.getpid(), executable
        try:
            # Every worker is constructed above with all three streams piped.
            stdin = cast(TextIO, _worker.stdin)
            stdin.write(json.dumps(request) + "\n")
            stdin.flush()
            response = cast(TextIO, _worker.stdout).readline()
            if not response:
                error = cast(TextIO, _worker.stderr).read()
                raise RuntimeError(f"verified Lean solver stopped: {error.strip()}")
            return json.loads(response)
        except (OSError, json.JSONDecodeError):
            _stop_worker()
            raise RuntimeError("invalid response from verified Lean solver") from None


def _lean_executable():
    override = os.environ.get("COMMON_SUBTREE_VERIFIED_LEAN")
    if override:
        candidates = [Path(override)]
    else:
        package = Path(__file__).resolve().parent
        name = "verified_ordered.exe" if os.name == "nt" else "verified_ordered"
        candidates = [package / "_bin" / name,
                      package.parent / "proofs" / ".lake" / "build" / "bin" / name]
    return next((path for path in candidates if path.is_file() and os.access(path, os.X_OK)), None)


def _encode(sequence, open_to_close):
    from .balanced_sequence import generate_balance

    # Validate typed nesting completely, including when the other side is empty.
    for _ in generate_balance(sequence, open_to_close):
        pass
    positions, children, parents, stack = [], [], [], []
    roots = []
    for position, token in enumerate(sequence):
        if token in open_to_close:
            index = len(positions)
            positions.append([position, None])
            children.append([])
            parents.append(stack[-1] if stack else None)
            (children[stack[-1]] if stack else roots).append(index)
            stack.append(index)
        else:
            positions[stack.pop()][1] = position
    following = {}
    for siblings in [roots, *children]:
        following.update(zip(siblings, siblings[1:]))
    encoded = [None] * len(positions)
    for index in reversed(range(len(positions))):
        head = encoded[children[index][0]] if children[index] else []
        tail = encoded[following[index]] if index in following else []
        encoded[index] = [index, head, tail]
    return (encoded[roots[0]] if roots else []), positions, parents


def _lcsi_verified_lean(seq1, seq2, open_to_close, open_to_node, node_affinity, *, rooted=False):
    from .balanced_sequence import _read_token_indices

    executable = _lean_executable()
    if executable is None:
        raise ImportError("verified-lean requires the compiled verified_ordered executable; "
                          "build with -DBUILD_LEAN_BACKEND=ON (see proofs/VERIFICATION.md)")
    left, lp, _ = _encode(seq1, open_to_close)
    right, rp, _ = _encode(seq2, open_to_close)
    if node_affinity is None:
        affinity = lambda a, b: 1
    elif isinstance(node_affinity, str):
        if node_affinity not in {"auto", "eq"}:
            raise ValueError("unknown node_affinity")
        affinity = operator.eq
    elif callable(node_affinity):
        affinity = node_affinity
    else:
        raise TypeError("node_affinity must be None, 'auto', 'eq', or callable")

    def node(sequence, position):
        token = sequence[position]
        return token if open_to_node is None else open_to_node[token]

    # Mapping values are fixed input data. Resolve once, as the Rust encoder does.
    left_nodes = [node(seq1, opening) for opening, _ in lp] if rp else []
    right_nodes = [node(seq2, opening) for opening, _ in rp] if lp else []
    weights = []
    for left_node in left_nodes:
        row = []
        for right_node in right_nodes:
            value = affinity(left_node, right_node)
            # Canonical built-ins already have an exact numerator and denominator.
            # Avoid an ABC lookup, copy and rational comparison for every cell.
            if type(value) is not int and type(value) is not Fraction:
                if not isinstance(value, Rational):
                    raise TypeError("verified-lean affinities must be exact Rational values "
                                    "(int or fractions.Fraction); floats require explicit conversion")
                value = Fraction(value)
            if value.numerator < 0:
                raise ValueError("node affinities must be nonnegative")
            row.append(value)
        weights.append(row)
    if not rp:
        weights = [[] for _ in lp]
    request = dict(protocol=1, left=left, right=right, rooted=rooted,
                   weights=[[[str(v.numerator), str(v.denominator)] for v in row] for row in weights])
    try:
        result = _request(executable, request)
        if "error" in result:
            raise ValueError(result["error"])
        if result["protocol"] != 1:
            raise RuntimeError("unsupported verified Lean response protocol")
        pairs = result["pairs"]
        left_ids, right_ids = [p[0] for p in pairs], [p[1] for p in pairs]
        if (any(type(i) is not int or not 0 <= i < len(lp) for i in left_ids) or
                any(type(i) is not int or not 0 <= i < len(rp) for i in right_ids) or
                len(set(left_ids)) != len(pairs) or len(set(right_ids)) != len(pairs)):
            raise RuntimeError("invalid original identities in verified Lean response")
        score = Fraction(int(result["numerator"]), int(result["denominator"]))
        if score != sum((weights[i][j] for i, j in pairs), Fraction()):
            raise RuntimeError("verified Lean witness score disagrees with original affinities")
        if any(weights[i][j].numerator <= 0 for i, j in pairs):
            raise RuntimeError("verified Lean witness includes a forbidden pair")
    except (KeyError, IndexError, json.JSONDecodeError) as exc:
        raise RuntimeError("invalid response from verified Lean solver") from exc
    li = sorted(position for i in left_ids for position in lp[i])
    ri = sorted(position for i in right_ids for position in rp[i])
    return (_read_token_indices(seq1, li), _read_token_indices(seq2, ri)), score
