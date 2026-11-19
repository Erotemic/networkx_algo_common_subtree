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


def _lcsi_iter_rust(full_seq1, full_seq2, open_to_close, node_affinity, open_to_node, *, rooted=False):
    backend = _rust_lcsi_backend(error="raise")
    subseq1, subseq2, value = backend.longest_common_balanced_isomorphism(
        full_seq1,
        full_seq2,
        open_to_close,
        open_to_node=open_to_node,
        node_affinity=node_affinity,
        rooted=rooted,
    )
    return (subseq1, subseq2), value


def _lcsi_reference_rust(seq1, seq2, open_to_close, *, rooted=False):
    """Use the structural reference with tested original-token reconstruction."""
    from .balanced_sequence import generate_balance, _read_token_indices

    backend = _rust_lcsi_backend(error="raise")
    if not hasattr(backend, "maximum_common_token_isomorphism"):
        raise ImportError("the Rust extension must be rebuilt for reference-rust")
    left = [token not in open_to_close for _, token, _ in generate_balance(seq1, open_to_close)]
    right = [token not in open_to_close for _, token, _ in generate_balance(seq2, open_to_close)]
    li, ri, score = backend.maximum_common_token_isomorphism(left, right, rooted=rooted)
    return (_read_token_indices(seq1, li), _read_token_indices(seq2, ri)), score
