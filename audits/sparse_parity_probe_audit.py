"""Check the single-flip exposure bound and its full-scan endpoint on small rows."""

from itertools import product


def query_program(row, first, after_zero, after_one, acceptance_mask):
    first_bit = (row >> first) & 1
    branch = after_one if first_bit else after_zero
    if branch < 0:
        # Early halt. Its outcome is independent of the unused second bit.
        second_bit = 0
        probes = 1 << first
    else:
        second_bit = (row >> branch) & 1
        probes = (1 << first) | (1 << branch)
    outcome = (acceptance_mask >> (2 * first_bit + second_bit)) & 1
    return outcome, probes


def main():
    n = 3
    programs = list(product(range(n), range(-1, n), range(-1, n), range(16)))
    traces = [
        [query_program(row, *program) for row in range(1 << n)]
        for program in programs
    ]
    checks = 0
    positive_cost_cases = 0
    # A four-tape strategy mixture. Individual queries depend on observed replies.
    for step in [1, 7, 41, 131]:
        for start in range(len(programs)):
            mixture = [traces[(start + step*i) % len(programs)] for i in range(4)]
            for row in range(1 << n):
                accepted = sum(t[row][0] for t in mixture)
                exposure = [sum((t[row][1] >> i) & 1 for t in mixture) for i in range(n)]
                least = min(range(n), key=exposure.__getitem__)
                changed = sum(t[row ^ (1 << least)][0] for t in mixture)
                assert accepted - changed <= exposure[least]
                assert n * (accepted - changed) <= sum(exposure)
                positive_cost_cases += accepted > changed
                checks += 1
    assert positive_cost_cases > 0

    # The maximal-count witness works on every row of weight m as long as
    # higher weights have ceased to occur. Try every list of positions.
    cap_tests = 0
    for m in range(n+1):
        for row in range(1 << n):
            if row.bit_count() > m:
                continue
            accepts = any(
                witness.bit_count() == m and witness & row == witness
                for witness in range(1 << n)
            )
            assert accepts == (row.bit_count() == m)
            cap_tests += 1
    print(f'{checks} adaptive mixture/row exposures and {cap_tests} maximal-count witnesses verified.')


if __name__ == '__main__':
    main()
