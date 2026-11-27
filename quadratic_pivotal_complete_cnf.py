"""Construct and check complete signed CNFs with many individually necessary clauses."""
from functools import cache
from itertools import combinations, product
from math import comb
from shutil import which
import subprocess

from single_support_seed_census import WITNESS


def bad_pattern(clause):
    return sum((literal < 0) << i for i, literal in enumerate(clause))


def build(width, group_sizes):
    """Return clauses, distinct target indices, private witnesses, total variable count."""
    assert width >= 3 and len(group_sizes) == width - 1 and min(group_sizes) >= 1
    seed, anchors = fixed_zero_seed(width)
    assert anchors >= width - 1
    clauses = {}
    def install(row):
        row = tuple(sorted(row, key=abs))
        key = tuple(map(abs, row))
        assert len(set(key)) == width and key not in clauses
        clauses[key] = row
        return key

    for row in seed:
        install(row)
    groups = []
    last = anchors
    for length in group_sizes:
        choice = list(range(last + 1, last + 1 + length))
        prefix = list(range(choice[-1] + 1, choice[-1] + length + 2))
        last = prefix[-1]
        groups.append((choice, prefix))
        install((*range(1, width), prefix[0]))
        install((*range(1, width), -prefix[-1]))
        for i, atom in enumerate(choice):
            install((*range(1, width - 2), -prefix[i], atom, prefix[i+1]))

    keys, rows = [], []
    for selected in product(*(range(length) for length in group_sizes)):
        keys.append(install((1, *(-choice[index] for index, (choice, _) in zip(selected, groups)))))
        row = 0
        for index, (choices, prefix) in zip(selected, groups):
            row |= 1 << (choices[index] - 1)
            for ground in prefix[:index+1]:
                row |= 1 << (ground-1)
        rows.append(row)

    coord = [0] + [sum(1 << i for i, row in enumerate(rows) if row >> (x-1) & 1)
                   for x in range(1, last + 1)]
    universe = (1 << len(rows)) - 1
    for support in combinations(range(1, last+1), width):
        if support in clauses:
            continue
        patterns = [universe]
        for x in support:
            patterns = [piece & ~coord[x] for piece in patterns] + [piece & coord[x] for piece in patterns]
        forbidden = patterns.index(0)
        install([-x if forbidden >> j & 1 else x for j, x in enumerate(support)])
    targets = {key: i for i, key in enumerate(keys)}
    assert len(clauses) == comb(last, width)
    for key, clause in clauses.items():
        viol = universe
        for literal in clause:
            viol &= coord[abs(literal)] if literal < 0 else universe ^ coord[literal]
        assert viol == (1 << targets[key] if key in targets else 0)
    return clauses, keys, rows, last


@cache
def fixed_zero_seed(width):
    """Provide reproducible, uniquely zero finite seeds for the audited widths."""
    if width == 3:
        return WITNESS, 5
    # Choose nonzero forbidden patterns on unused supports by largest coverage.
    # Only these fixed finite widths rely on the greedy selection.
    m = {4: 8, 5: 11}[width]
    coords = list(combinations(range(m), width))
    truth = (1 << (1 << m)) - 1
    bits = [sum(1 << a for a in range(1 << m) if a >> i & 1) for i in range(m)]
    uncovered = truth ^ 1
    masks = []
    for xs in coords:
        found = [truth]
        for x in xs:
            found = [v & ~bits[x] for v in found] + [v & bits[x] for v in found]
        masks.append(found)
    available = set(range(len(coords)))
    chosen = {}
    while uncovered:
        _, i, p = max(((masks[i][p] & uncovered).bit_count(), i, p)
                      for i in available for p in range(1, 1 << width))
        count = (masks[i][p] & uncovered).bit_count()
        assert count > 0, (width, uncovered.bit_count())
        chosen[i] = p
        available.remove(i)
        uncovered &= ~masks[i][p]
    result = tuple(tuple(-(x+1) if chosen.get(i, 1) >> j & 1 else x+1
                         for j, x in enumerate(xs)) for i, xs in enumerate(coords))
    assert not any(bad_pattern(c) == 0 for c in result)
    return result, m


def verify_unsat(rows, n, solver):
    text = f"p cnf {n} {len(rows)}\n" + ''.join(' '.join(map(str, row)) + ' 0\n' for row in rows)
    result = subprocess.run([solver, '-q'], input=text, text=True, capture_output=True)
    assert result.returncode == 20 and 's UNSATISFIABLE' in result.stdout


def main():
    solver = which('cadical')
    instances = pivots = supports = 0
    for k, sizes in [(3, (1, 1)), (3, (2, 3)), (3, (4, 4)), (3, (7, 8)),
                     (4, (2, 2, 3)), (5, (1, 1, 2, 2))]:
        clauses, keys, private, v = build(k, sizes)
        if solver:
            verify_unsat(clauses.values(), v, solver)
        assert len(private) == len(set(private)) == len(keys)
        assert len(clauses) == comb(v, k)
        if k == 3 and sizes == (1, 1):
            for key in keys:
                models = [x for x in range(1 << v) if all(
                    any(bool(x >> (abs(l)-1) & 1) == (l > 0) for l in row)
                    for supp, row in clauses.items() if supp != key)]
                assert private[keys.index(key)] in models
        instances += 1
        pivots += len(keys)
        supports += len(clauses)
    print(f'{instances} complete CNFs, {pivots} private witnesses, {supports} signed supports; '
          f'counterfactuals hold; independent SAT refutations {instances if solver else 0}.')


if __name__ == '__main__':
    main()
