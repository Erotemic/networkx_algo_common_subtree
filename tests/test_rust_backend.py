import pytest

from networkx_algo_common_subtree import balanced_embedding
from networkx_algo_common_subtree import balanced_isomorphism


def test_rust_auto_backend_preference_embedding():
    pytest.importorskip("networkx_algo_common_subtree._rust")
    seq1 = "[][[]][]"
    seq2 = "[[]][[]]"
    open_to_close = {"[": "]"}

    best_auto, value_auto = balanced_embedding.longest_common_balanced_embedding(
        seq1, seq2, open_to_close, impl="auto"
    )
    best_rust, value_rust = balanced_embedding.longest_common_balanced_embedding(
        seq1, seq2, open_to_close, impl="iter-rust"
    )
    assert value_auto == value_rust
    assert best_auto == best_rust


def test_rust_auto_backend_preference_isomorphism():
    pytest.importorskip("networkx_algo_common_subtree._rust")
    seq1 = "[][[]][]"
    seq2 = "[[]][[]]"
    open_to_close = {"[": "]"}

    best_auto, value_auto = balanced_isomorphism.longest_common_balanced_isomorphism(
        seq1, seq2, open_to_close, impl="auto"
    )
    best_rust, value_rust = balanced_isomorphism.longest_common_balanced_isomorphism(
        seq1, seq2, open_to_close, impl="iter-rust"
    )
    assert value_auto == value_rust
    assert best_auto == best_rust


def test_python_cython_rust_agree_on_small_examples():
    examples = [
        ("[][[]][]", "[[]][[]]", {"[": "]"}),
        ("0010010010111100001011011011", "001000101101110001000100101110111011", {"0": "1"}),
    ]

    emb_impls = balanced_embedding.available_impls_longest_common_balanced_embedding()
    iso_impls = balanced_isomorphism.available_impls_longest_common_balanced_isomorphism()

    for seq1, seq2, open_to_close in examples:
        emb_values = {}
        for impl in emb_impls:
            _, value = balanced_embedding.longest_common_balanced_embedding(
                seq1, seq2, open_to_close, impl=impl
            )
            emb_values[impl] = value
        assert len(set(emb_values.values())) == 1

        iso_values = {}
        for impl in iso_impls:
            _, value = balanced_isomorphism.longest_common_balanced_isomorphism(
                seq1, seq2, open_to_close, impl=impl
            )
            iso_values[impl] = value
        assert len(set(iso_values.values())) == 1


def test_rust_impl_registration_behavior():
    emb_impls = balanced_embedding.available_impls_longest_common_balanced_embedding()
    iso_impls = balanced_isomorphism.available_impls_longest_common_balanced_isomorphism()
    try:
        import networkx_algo_common_subtree._rust  # NOQA
    except Exception:
        assert "iter-rust" not in emb_impls
        assert "iter-rust" not in iso_impls
    else:
        assert "iter-rust" in emb_impls
        assert "iter-rust" in iso_impls
