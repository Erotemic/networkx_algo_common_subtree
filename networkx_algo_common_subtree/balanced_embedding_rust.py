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
    subseq1, subseq2, value = backend.longest_common_balanced_embedding(
        full_seq1,
        full_seq2,
        open_to_close,
        open_to_node=open_to_node,
        node_affinity=node_affinity,
    )
    return value, (subseq1, subseq2)


def _lcse_verified_rust(seq1, seq2, open_to_close):
    """Adapt validated typed tokens to the proved unweighted Boolean core.

    The Python token conversion and extension boundary are tested integration;
    the Lean theorem covers the Rust Boolean core and its returned indices.
    """
    from .balanced_sequence import generate_balance, _read_token_indices

    backend = _rust_lcse_backend(error="raise")
    if not hasattr(backend, "maximum_common_token_embedding"):
        raise ImportError("the Rust extension must be rebuilt for verified-rust")

    # Exhaust each generator so mismatched token kinds and incomplete pairs
    # are rejected before type erasure, including an unclosed final pair.
    left = [token not in open_to_close for _, token, _ in generate_balance(seq1, open_to_close)]
    right = [token not in open_to_close for _, token, _ in generate_balance(seq2, open_to_close)]
    left_indices, right_indices, value = backend.maximum_common_token_embedding(left, right)

    return (_read_token_indices(seq1, left_indices), _read_token_indices(seq2, right_indices)), value
