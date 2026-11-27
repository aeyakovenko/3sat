"""Check the signed unit-CNF transfer on all small inputs and row labels."""
from itertools import combinations, count, product
from random import Random


def word_ram_unit_sat(positive, negative, address_count):
    """Unit clauses on fixed-width binary identifiers using direct addressing."""
    memory = bytearray(address_count)
    for address in positive:
        memory[address] = 1
    return not any(memory[address] for address in negative)


def check_input(values, alphabet):
    n = len(values)
    # Positive variables contain the source position as well as its value.
    positive = tuple(i * alphabet + value for i, value in enumerate(values))
    positive_set = set(positive)
    reserve_start = n * alphabet
    signs = [(-1) ** mask.bit_count() for mask in range(1 << n)]
    total = 0
    survivor = []
    formula_count = 0
    row_count = 0
    for targets in combinations(range(alphabet), n):
        for labels in product(range(n), repeat=n):
            target_names = tuple(i * alphabet + y for i, y in zip(labels, targets))
            expected = all(address in positive_set for address in target_names)
            weight = 0
            for mask, sign in enumerate(signs):
                negative = tuple(address if (mask >> j) & 1 else reserve_start + j
                                 for j, address in enumerate(target_names))
                # Each bank contributes at most one occurrence of any name.
                assert len(positive_set) == n and len(set(negative)) == n
                answer = word_ram_unit_sat(positive, negative, reserve_start + n)
                assert answer == positive_set.isdisjoint(negative)
                weight += sign * answer
                formula_count += 1
            assert weight == int(expected)
            if weight:
                survivor.append((targets, labels))
            row_count += 1
            total += weight
    distinct = len(set(values)) == n
    assert total == int(distinct)
    for characteristic in (2, 3, 5):
        assert total % characteristic == int(distinct)
    if distinct:
        targets = tuple(sorted(values))
        assert survivor == [(targets, tuple(values.index(y) for y in targets))]
    else:
        assert not survivor
    return row_count, formula_count


def duplicate_cnf(values):
    """Generate the direct projection with a dense positive variable namespace."""
    n = len(values)
    assert n >= 2 and n & (n - 1) == 0
    assert all(0 <= x < n * n for x in values)
    high = range(n, 2 * n)
    low = range(2 * n, 3 * n)
    selected = [*range(1, n), 3 * n]
    fresh = count(3 * n + 1)
    clauses = []
    for i, value in enumerate(values):
        # The two names consist of a constant prefix and untouched input bits.
        clauses.extend([(-selected[i], high[value // n]),
                        (-selected[i], low[value % n])])

    for bank in (high, low):
        prev = next(fresh)
        clauses.append((-prev,))
        for flag in bank:
            curr = next(fresh)
            clauses.extend([(-flag, curr), (-prev, curr), (-flag, -prev)])
            prev = curr

    def or_gate(a, b):
        out = next(fresh)
        clauses.extend([(-a, out), (-b, out), (a, b, -out)])
        return out

    def and_gate(a, b):
        out = next(fresh)
        clauses.extend([(a, -out), (b, -out), (-a, -b, out)])
        return out

    seen, pair = next(fresh), next(fresh)
    clauses.extend([(-seen,), (-pair,)])
    for choice in selected:
        pair = or_gate(pair, and_gate(seen, choice))
        seen = or_gate(seen, choice)
    clauses.append((pair,))
    return clauses, next(fresh), next(fresh)


def strict_padding(clauses, pad_a, pad_b):
    strict = []
    for row in clauses:
        pads = (pad_a, pad_b)[:3 - len(row)]
        for signs in product((-1, 1), repeat=len(pads)):
            strict.append(row + tuple(v * s for v, s in zip(pads, signs)))
    return strict


def restrict(clauses, lit):
    return [tuple(x for x in row if x != -lit) for row in clauses if lit not in row]


def cnf_sat(clauses):
    """A complete branching solver independent of the projection invariant."""
    while clauses:
        row = min(clauses, key=len)
        if not row:
            return False
        if len(row) == 1:
            clauses = restrict(clauses, row[0])
        else:
            return any(cnf_sat(restrict(clauses, lit)) for lit in (row[0], -row[0]))
    return True


def check_direct_projection():
    rng = Random(4107)
    samples = list(product(range(4), repeat=2))
    samples += list(product((0, 3, 12, 15), repeat=4))
    samples += [tuple(rng.randrange(16) for _ in range(4)) for _ in range(120)]
    samples += [tuple(rng.randrange(64) for _ in range(8)) for _ in range(20)]
    for values in samples:
        clauses, pad_a, pad_b = duplicate_cnf(values)
        strict = strict_padding(clauses, pad_a, pad_b)
        assert all(len(row) == len(set(map(abs, row))) == 3 for row in strict)
        assert {abs(lit) for row in strict for lit in row} == set(range(1, pad_b + 1))
        expected_rows = set(clauses)
        for a, b in product((-1, 1), repeat=2):
            assert set(restrict(restrict(strict, a * pad_a), b * pad_b)) == expected_rows
        assert cnf_sat(clauses) == (len(set(values)) < len(values))
    return len(samples)


def main():
    input_count = row_count = formula_count = 0
    for n, alphabet in ((1, 2), (2, 4), (3, 4), (4, 4)):
        for values in product(range(alphabet), repeat=n):
            rows, formulas = check_input(values, alphabet)
            input_count += 1
            row_count += rows
            formula_count += formulas
    print(f'{input_count} source lists, {row_count} sorted target and row-label '
          f'guesses, {formula_count} two-occurrence unit formulas; '
          'signed transfer exact over the integers and modulo 2, 3, and 5.')
    print(f'{check_direct_projection()} direct dense 3-CNF instances checked '
          'with complete SAT search and all four strict-padding restrictions.')


if __name__ == '__main__':
    main()
