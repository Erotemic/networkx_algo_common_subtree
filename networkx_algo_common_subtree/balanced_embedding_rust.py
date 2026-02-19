"""Rust backend shim for balanced embedding."""


def _rust_lcse_backend(error="ignore"):
    try:
        from . import _rust
    except Exception:
        if error == "ignore":
            _rust = None
        elif error == "raise":
            raise
        else:
            raise KeyError(error)
    return _rust


def _lcse_iter_rust(full_seq1, full_seq2, open_to_close, node_affinity, open_to_node):
    backend = _rust_lcse_backend(error="raise")
    best, value = backend.longest_common_balanced_embedding(
        full_seq1,
        full_seq2,
        open_to_close,
        open_to_node=open_to_node,
        node_affinity=node_affinity,
    )
    return value, best
