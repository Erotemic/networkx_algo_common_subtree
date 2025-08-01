import timerit
from networkx_algo_common_subtree import balanced_embedding, balanced_sequence


def main():
    seq_len = 200
    seq1, otc1 = balanced_sequence.random_balanced_sequence(seq_len, item_type='paren', container_type='str')
    seq2, otc2 = balanced_sequence.random_balanced_sequence(seq_len, item_type='paren', container_type='str')
    open_to_close = {**otc1, **otc2}

    best_base, val_base = balanced_embedding.longest_common_balanced_embedding(
        seq1, seq2, open_to_close, impl='iter-cython'
    )
    best_alt, val_alt = balanced_embedding.longest_common_balanced_embedding(
        seq1, seq2, open_to_close, impl='iter-cython-alt'
    )
    assert val_base == val_alt
    assert best_base == best_alt

    ti = timerit.Timerit(3, bestof=3, verbose=2)
    for impl in ['iter-cython', 'iter-cython-alt']:
        for timer in ti.reset(impl):
            with timer:
                balanced_embedding.longest_common_balanced_embedding(
                    seq1, seq2, open_to_close, impl=impl
                )
    print('Timing results:')
    for impl, times in ti.result.items():
        print(f'{impl}: {times.mean():.6f}s')
    print('Speedup: {:.2f}x'.format(ti.result['iter-cython'].mean() / ti.result['iter-cython-alt'].mean()))


if __name__ == '__main__':
    main()
