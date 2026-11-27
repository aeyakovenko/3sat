"""Exhaust small first-failed prefixes and read probes from every Hall pair."""

from itertools import permutations, product

from first_missing_offer_audit import first_deficient_prefix


def witnesses(rows, n):
    first = first_deficient_prefix(rows, n)
    full = (1 << n) - 1
    for subset in range(1, 1 << (first + 1)):
        neighbors = 0
        for h, row in enumerate(rows[:first + 1]):
            if subset & (1 << h):
                neighbors |= row
        for columns in range(1 << n):
            # Any advertised set with bounded excess and uncovered neighbors.
            slack = max(0, columns.bit_count() - (subset.bit_count() - 1))
            uncovered = (neighbors & ~columns).bit_count()
            assert (columns & ~neighbors).bit_count() <= slack + uncovered
            if not slack and not uncovered:
                assert subset & (1 << first)
                assert columns == neighbors and columns.bit_count() + 1 == subset.bit_count()
                # Each constant column separately extracts its truth value.
                for e in range(n):
                    values = {bool(row & (1 << e)) for row in rows}
                    if len(values) == 1:
                        assert bool(columns & (1 << e)) == values.pop()
                yield columns & full


def check_all_graphs(n):
    count = 0
    matching_count = 0
    for rows in product(range(1 << n), repeat=n + 1):
        pairs = list(witnesses(rows, n))
        assert pairs
        count += len(pairs)
        first = first_deficient_prefix(rows, n)
        for codes in permutations(range(n), first):
            if all(rows[h] & (1 << c) for h, c in enumerate(codes)):
                matching_count += 1
                for c in range(n):
                    values = {bool(row & (1 << c)) for row in rows}
                    if len(values) == 1:
                        assert (c in codes) == values.pop()
    print(f'{n} codes, {1 << (n * (n + 1))} graphs, {count} Hall pairs, '
          f'{matching_count} positive prefix matchings')


def check_thresholds():
    # Three inner prefix predicates plus two arbitrary varying outer columns.
    n, width = 5, 3
    probe_mask = (1 << width) - 1
    pairs = 0
    for cut in range(width + 1):
        wanted = (1 << cut) - 1
        for other in product(range(1 << (n - width)), repeat=n + 1):
            rows = [wanted | (part << width) for part in other]
            for columns in witnesses(rows, n):
                assert columns & probe_mask == wanted
                pairs += 1
    print(f'3 threshold probes with 2 other columns, {pairs} exact Hall pairs')


def check_noise_boundary():
    # The same approximate neighborhood can describe two opposite probe bits.
    for slack, erasures in product(range(4), repeat=2):
        copies = slack + 2 * erasures
        if not copies:
            continue
        probes = set(range(copies))
        other = set(range(copies, 2 * copies))
        observed = set(range(copies - erasures)) | set(range(copies, 2 * copies - erasures))
        for neighbors in (probes, other):
            # Every row has these same neighbors, so the first copies rows
            # match and the next fails. Its Hall set consists of all rows.
            assert len(neighbors) == copies
            assert len(observed) == copies + slack
            assert len(neighbors - observed) == erasures
        assert len(observed & probes) == copies - erasures


if __name__ == '__main__':
    for size in range(1, 4):
        check_all_graphs(size)
    check_thresholds()
    check_noise_boundary()
