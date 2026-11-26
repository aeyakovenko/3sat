"""Exhaust small Hankel templates, their dual certificates, and sparse equations."""

from itertools import product


def coefficients(values, prime):
    result = list(values)
    for i in range((len(values) - 1).bit_length()):
        bit = 1 << i
        for mask in range(len(values)):
            if mask & bit:
                result[mask] = (result[mask] - result[mask ^ bit]) % prime
    return result


def check_sparse_product():
    count = 0
    for prime, dimensions in ((2, range(5)), (3, range(4))):
        for m in dimensions:
            for values in product(range(prime), repeat=1 << m):
                nonzero = [word for word, value in enumerate(values) if value]
                if not nonzero:
                    continue
                sparsity = sum(value != 0 for value in coefficients(values, prime))
                largest_face = max(m - word.bit_count() for word in nonzero)
                assert len(nonzero) * sparsity >= 1 << largest_face
                count += 1
    return count


def extension(seed, polynomial, order, length):
    word = seed
    mask = (1 << order) - 1
    for i in range(length - order):
        window = (word >> i) & mask
        bit = (window & polynomial).bit_count() & 1
        word |= bit << (i + order)
    return word


def linear_test(word, order, length):
    """Eliminate augmented rows, tracking the original indices proving 0 = 1."""
    mask = (1 << order) - 1
    basis = {}
    for i in range(length - order):
        row = (word >> i) & mask
        rhs = (word >> (i + order)) & 1
        source = 1 << i
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (row, rhs, source)
                break
            other, value, indices = basis[pivot]
            row ^= other
            rhs ^= value
            source ^= indices
        if row == 0 and rhs:
            assert source.bit_count() <= order + 1
            return source
    return 0


def check_hankel():
    total = certificates = 0
    for order in range(1, 5):
        for length in range(2 * order, 13):
            all_words = set()
            predict = {}
            chosen = {}
            for seed, polynomial in product(range(1 << order), repeat=2):
                word = extension(seed, polynomial, order, length)
                all_words.add(word)
                key = word % (1 << (2 * order))
                assert predict.setdefault(key, word) == word
                chosen.setdefault(key, polynomial)
            for word in range(1 << length):
                sources = linear_test(word, order, length)
                key = word % (1 << (2 * order))
                assert (word in all_words) == (sources == 0) == (predict.get(key) == word)
                if sources:
                    if key in chosen:
                        polynomial = chosen[key]
                        failures = [
                            i for i in range(length - order)
                            if (((word >> i) & polynomial).bit_count() & 1) != ((word >> (i + order)) & 1)
                        ]
                        assert failures
                        block = failures[0] // order
                        data_window = word >> (block * order)
                        assert any(
                            (((data_window >> j) & polynomial).bit_count() & 1)
                            != ((data_window >> (j + order)) & 1)
                            for j in range(min(order, length - order - block * order))
                        )
                    rhs_row = 0
                    for i in range(length - order):
                        if (sources >> i) & 1:
                            rhs_row ^= (word >> i) % (1 << (order + 1))
                    assert rhs_row == 1 << order
                    certificates += 1
                total += 1
    return total, certificates


def check_basis_changes():
    m = 3
    exceptional = {extension(seed, poly, 1, m) for seed, poly in product(range(2), repeat=2)}
    bases = rows = 0
    for linear in product(range(1, 1 << m), repeat=m):
        image = [
            sum(((v & form).bit_count() % 2) << i for i, form in enumerate(linear))
            for v in range(1 << m)
        ]
        if len(set(image)) < 1 << m:
            continue
        for shift in range(1 << m):
            bad = sorted(image[v] ^ shift for v in exceptional)
            target = min(bad, key=int.bit_count)
            for pattern in range(1 << len(bad)):
                selected = {v for i, v in enumerate(bad) if pattern >> i & 1}
                if target not in selected:
                    continue
                truth = [int(v in selected) for v in range(1 << m)]
                terms = sum(coefficients(truth, 2))
                assert terms * len(bad) >= 1 << (m - target.bit_count())
                rows += 1
            bases += 1
    return bases, rows


if __name__ == "__main__":
    checks = check_sparse_product()
    words, witnesses = check_hankel()
    bases, rows = check_basis_changes()
    print(f"{checks} nonzero value tables over F2 and F3")
    print(f"{words} Hankel words, {witnesses} checked dual inconsistencies")
    print(f"{bases} affine coordinates and {rows} separating polynomial rows")
