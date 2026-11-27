"""Exhaustive finite checks of pivot forcing and finite-injury accounting."""

from itertools import combinations, product


def triangularize(rows):
    """Reduce augmented binary rows by the rightmost occupied column."""
    basis = {}
    for mask, rhs in rows:
        while mask:
            pivot = mask.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = mask, rhs
                break
            earlier_mask, earlier_rhs = basis[pivot]
            mask ^= earlier_mask
            rhs ^= earlier_rhs
        else:
            if rhs:
                return None
    return sorted(basis.items())


def agrees(word, rows):
    return all((word & mask).bit_count() % 2 == rhs for mask, rhs in rows)


def force(word, basis):
    for p, (mask, rhs) in basis:
        if (word & mask).bit_count() % 2 != rhs:
            word ^= 1 << p
    return word


def check_flats():
    count = 0
    for width in range(1, 5):
        equations = [(mask, rhs) for mask in range(1, 1 << width)
                     for rhs in range(2)]
        for length in range(1, 4):
            for rows in combinations(equations, length):
                basis = triangularize(rows)
                words = range(1 << width)
                actual = [word for word in words if agrees(word, rows)]
                assert (basis is None) == (not actual)
                if basis is None:
                    continue
                pivot_mask = sum(1 << p for p, _ in basis)
                for word in words:
                    result = force(word, basis)
                    assert result in actual
                    assert (word ^ result) & ~pivot_mask == 0
                    assert (word ^ result).bit_count() <= len(basis)
                count += 1
    return count


def check_interruptions():
    # All possible rank-start sequences through five stages, with all possible
    # immediate/delayed completion decisions for the current pending rank.
    # An integer code 0 means nobody applies; 1..3 each denote one candidate.
    checked = 0
    for applications in product(range(4), repeat=5):
        for finish in product(range(2), repeat=5):
            pending = None
            retired = set()
            starts = [0] * 3
            for applicant, completes in zip(applications, finish):
                rank = applicant - 1
                if rank >= 0 and rank not in retired and (pending is None or rank < pending):
                    pending = rank
                    starts[rank] += 1
                if pending is not None and completes:
                    retired.add(pending)
                    pending = None
            for e, count in enumerate(starts):
                assert count <= 1 + sum(starts[:e])
                assert count <= 2**e
            for capacity in [4, 31, 64, 257]:
                paid = sum((capacity // 4**(e+1)) * n for e, n in enumerate(starts))
                assert 2 * paid <= capacity
            checked += 1
    return checked


def check_sparse_exclusions():
    # Tight elementary geometry: every consistent rank-r system admits a
    # solution of weight at most r (start from zero and force its pivots).
    # The extremizing all-ones coordinate flat has minimum weight exactly r.
    count = 0
    for width in range(1, 9):
        for rank in range(1, width + 1):
            for selected in combinations(range(width), rank):
                mask = sum(1 << i for i in selected)
                minimum = min(word.bit_count() for word in range(1 << width)
                              if word & mask == mask)
                assert minimum == rank
                count += 1
    assert count == sum(2**i - 1 for i in range(1, 9))
    return count


if __name__ == '__main__':
    print(f'{check_flats()} nonempty affine systems forced from every starting word')
    print(f'{check_interruptions()} priority request and completion schedules checked')
    print(f'{check_sparse_exclusions()} sparse-coordinate exclusions checked')
