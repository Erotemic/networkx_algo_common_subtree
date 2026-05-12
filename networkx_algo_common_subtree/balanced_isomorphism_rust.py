"""Rust backend shim for balanced isomorphism."""


def _rust_lcsi_backend(error="ignore"):
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


def _lcsi_iter_rust(full_seq1, full_seq2, open_to_close, node_affinity, open_to_node):
    backend = _rust_lcsi_backend(error="raise")
    subseq1, subseq2, value = backend.longest_common_balanced_isomorphism(
        full_seq1,
        full_seq2,
        open_to_close,
        open_to_node=open_to_node,
        node_affinity=node_affinity,
    )
    return (subseq1, subseq2), value
