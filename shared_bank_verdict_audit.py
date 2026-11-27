"""Exhaust small affine bank tests and replay an indexed proper 3-SAT batch."""

from itertools import combinations, product


def rref_bases(width, rank):
    """Binary row spaces, using the least nonzero column as a row pivot."""
    for pivots in combinations(range(width), rank):
        free = [(row, col) for row, pivot in enumerate(pivots)
                for col in range(pivot + 1, width) if col not in pivots]
        for choices in range(1 << len(free)):
            rows = [1 << pivot for pivot in pivots]
            for k, (row, col) in enumerate(free):
                if choices >> k & 1:
                    rows[row] |= 1 << col
            yield tuple(rows)


def read_schedule(d, h):
    for i in range(d):
        yield i
        yield d + i + h
    yield d + h
    yield d + 2 * h


def correction(bank, d, h):
    values = iter((bank >> addr) & 1 for addr in read_schedule(d, h))
    result = 0
    for _ in range(d):
        result ^= next(values) & next(values)
    return result ^ next(values) ^ next(values)


def audit(d, m):
    width = 2 * d + m - 1
    banks = range(1 << width)
    u_count = 1 << d
    answers = [sum(correction(bank, d, h) << h for h in range(m)) for bank in banks]
    marks = [1 << value for value in answers]
    all_outputs = (1 << (1 << m)) - 1
    u_values = [bank % u_count for bank in banks]
    characters = [[(row & bank).bit_count() % 2 for bank in banks] for row in range(1 << width)]
    totals = 0
    for rank in range(d - m + 1):
        assert rank <= 2  # The proof allows arbitrary rank; the census uses at most two rows.
        for rows in rref_bases(width, rank):
            if rank == 0:
                cosets = [0] * len(banks)
            elif rank == 1:
                cosets = characters[rows[0]]
            else:
                cosets = [x | (y << 1) for x, y in zip(characters[rows[0]], characters[rows[1]])]
            by_coset = [[0] * u_count for _ in range(1 << rank)]
            for coset, u, mark in zip(cosets, u_values, marks):
                by_coset[coset][u] |= mark
            for per_u in by_coset:
                assert all_outputs in per_u  # One fixed first bank covers every verdict vector.
                if rank < d - m:
                    feasible = sum(bool(mask) for mask in per_u)
                    assert 2 * per_u.count(all_outputs) > feasible
            totals += 1 << rank
    sharp = 1 | ((u_count - 1) ^ ((1 << m) - 1))
    assert sharp.bit_count() == d - m + 1
    assert 1 not in {answers[bank] for bank in banks if not (bank & sharp)}
    return totals


def check_sat_batch():
    d, m = 5, 3
    # All eight clauses on variables 1,2,3 exclude all assignments. For SAT
    # payloads repeat the preceding clause in place of the final one.
    all_clauses = [tuple(v if key >> j & 1 else -v for j, v in enumerate((1, 2, 3)))
                   for key in range(8)]
    verdicts = []
    for h in range(m):
        payload = all_clauses.copy()
        if h != 1:
            payload[-1] = payload[-2]
        tags = [(4 if h & 1 else -4, 5, 6), (7 if h & 2 else -7, 8, 9)]
        rows = tags + payload
        verdicts.append(any(all(any(bits[abs(v)-1] == (v > 0) for v in clause) for clause in rows)
                            for bits in product((False, True), repeat=9)))
    assert verdicts == [True, False, True]
    real = sum(bit << i for i, bit in enumerate(verdicts))
    # Repeated reads in all C tapes use this same address-to-bit dictionary.
    # The adaptive second probe depends on the first numerical reply. We
    # follow its honest zero-bank branch through two independent restrictions.
    offered = set()
    for bank in range(1 << (2*d + m - 1)):
        first = ((bank & 0b10101).bit_count() & 1) ^ 1
        second_mask = 0b1110001 if first else 0b100
        second = (bank & second_mask).bit_count() & 1
        if (first, second) == (1, 0):
            errors = sum(correction(bank, d, i) << i for i in range(m))
            offered.add(real ^ errors)
    assert offered == set(range(1 << m))


if __name__ == '__main__':
    for d, m in [(2, 1), (3, 1), (3, 2), (4, 2), (4, 3)]:
        print(f'd={d} m={m}: {audit(d, m):,} affine fibers')
    check_sat_batch()
    print('The shared adaptive history realizes all eight verdict vectors on the legal batch.')
