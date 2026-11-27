"""Check the literal projection on actual compiled CNFs and exhaust its resolution rule."""

from collections import Counter
from itertools import combinations

from almost_mixed_cutoff_audit import signed_catalog, two_exception_formula
from one_byte_dense_successor_audit import parse


def substitution(source, compiled_variables):
    """Allocation order of the NAE compiler. The extra target name denotes TRUE."""
    top = max((abs(lit) for row in source for lit in row), default=0) + 1
    atoms = [None, top, -top, -top]  # one nonconstant root triple
    for _ in range(3):
        atoms.extend([top, top, -top, -top])
    occurrences = Counter()
    for row in source:
        for lit in row:
            atoms.append(abs(lit))
            occurrences[abs(lit)] += 1
    links = sum(count for count in occurrences.values() if count > 1)
    for size, value in ((4 * len(source), top), (4 * (len(source) + links), -top)):
        if size:
            for _ in range(6):
                atoms.extend([value, -top])  # first descendant and unconstrained guard
                atoms.extend([value] * size)
    for a, _, c in source:
        atoms.extend([-top] * 5 + [top] * 5 + [a, -c])
    atoms.extend([-top] * (5 * links))
    unregularized = len(atoms) - 1
    assert compiled_variables >= unregularized
    atoms.extend([-top] * (compiled_variables - unregularized))
    return top, atoms, unregularized


def all_physical_projections():
    catalog = signed_catalog()
    formulas = rows_seen = 0
    for mask in range(256):
        source = [row for i, row in enumerate(catalog) if mask & (1 << i)]
        for regular in (False, True):
            rows = parse(two_exception_formula(source, regular=regular))
            degree = Counter(abs(lit) for row in rows for lit in row)
            assert set(degree.values()) <= {1, 2, 3, 4}
            if regular:
                assert set(degree.values()) == {4}
            top, atoms, original = substitution(source, max(degree))
            assert regular or original == max(degree)
            surviving = []
            for row in rows:
                projected = {atoms[lit] if lit > 0 else -atoms[-lit] for lit in row}
                if top in projected or any(-x in projected for x in projected):
                    continue
                surviving.append(frozenset(projected - {-top}))
            assert Counter(surviving) == Counter(frozenset(row) for row in source)
            rows_seen += len(rows)
            formulas += 1
    return formulas, rows_seen


def subsets(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        for xs in combinations(values, size):
            yield frozenset(xs)


def local_resolution_checks():
    target = (1, -1, 2, -2)
    top = 3

    def normalize(literals):
        if top in literals or any(-x in literals for x in literals):
            return None
        return literals - {-top}

    checks = 0
    branches = set()
    for a in subsets(target):
        for b in subsets(target):
            result = normalize(a | b)
            if result is None:
                continue
            for pivot in target + (top, -top):
                left = normalize(a | {pivot})
                right = normalize(b | {-pivot})
                for d in [None] if left is None else subsets(left):
                    for e in [None] if right is None else subsets(right):
                        if d is not None and d <= result:
                            surviving = d
                            branches.add('left')
                        elif e is not None and e <= result:
                            surviving = e
                            branches.add('right')
                        else:
                            assert d is not None and e is not None
                            assert pivot in d and -pivot in e and pivot in target
                            surviving = (d - {pivot}) | (e - {-pivot})
                            branches.add('resolve')
                        assert surviving <= result
                        checks += 1
    assert branches == {'left', 'right', 'resolve'}
    return checks


if __name__ == '__main__':
    checks = local_resolution_checks()
    count, lines = all_physical_projections()
    print(f'{checks:,} resolution steps with projected subclauses, constants and identified literals')
    print(f'{count:,} parsed degree-four CNFs; {lines:,} projected clauses; every surviving multiset equals its source')
