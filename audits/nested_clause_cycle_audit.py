"""Check small one-clause extensions, terminal cuts and physically adjacent pinned files."""

from argparse import ArgumentParser
from functools import cache
from itertools import combinations, product
from subprocess import run


def clause_histories(width):
    if width == 3:
        yield (7,)
        return
    for history in clause_histories(width - 1):
        eligible = [j for j in range(width - 1) if sum((c >> j) & 1 for c in history) < 4]
        for a, b in combinations(eligible, 2):
            yield (*history, (1 << (width - 1)) | (1 << a) | (1 << b))


def subsets(mask):
    points = [0]
    while mask:
        v = mask & -mask
        points.extend([p | v for p in points])
        mask ^= v
    return points


def flattening_rows(width, history, mask):
    cols = subsets(((1 << width) - 1) ^ mask)
    return tuple(sum(1 << j for j, y in enumerate(cols) if all(c & (x | y) for c in history))
                 for x in subsets(mask))


def fits_two_rectangles(rows):
    nonempty = set(rows) - {0}
    if len(nonempty) <= 2:
        return True
    return len(nonempty) == 3 and any((u | v) in nonempty - {u, v} for u, v in combinations(nonempty, 2))


def tree_passes_cut_tests(width, history):
    # Necessary condition only, except when an explicit tree is supplied below.
    @cache
    def possible(mask):
        if mask.bit_count() <= 1:
            return True
        if not fits_two_rectangles(flattening_rows(width, history, mask)):
            return False
        for left in subsets(mask ^ (mask & -mask))[1:]:
            if possible(left) and possible(mask ^ left):
                return True
        return False

    return possible((1 << (width - 1)) - 1)


def prescribed_file(width, history, assignment):
    # Three distinct guard variables. The seven clauses leave only 000.
    rows = [tuple(-j if (v >> (j-1)) & 1 else j for j in (1, 2, 3)) for v in range(1, 8)]
    for i in range(width):
        pos = 10 * (i+1) + 2
        neg = pos+1
        rows.extend([(pos, neg, 1), (-pos, -neg, 1), (pos if assignment & (1 << i) else neg, 1, 2)])
    for clause in history:
        rows.append(tuple(10 * (j+1) + 2 for j in range(width) if clause & (1 << j)))
    assert all(len(row) == 3 and len({abs(k) for k in row}) == 3 for row in rows)
    last = 10 * width + 3
    digits = len(str(last)) + 1
    header = f'p cnf {last} {len(rows)}\n'
    body = ''.join(' '.join(f'{k:{digits}d}' for k in row) + ' 0\n' for row in rows)
    return (header+body).encode('ascii')


def run_audit(solver):
    for width in (3, 4, 5):
        viable = 0
        tested = 0
        changes = 0
        histories = list(clause_histories(width))
        for history in histories:
            tree_possible = tree_passes_cut_tests(width, history)
            common = history[0]
            for clause in history[1:]:
                common &= clause
            if width < 5 or common.bit_count() == 2:
                # Two common literals and one private literal per clause give a read-once formula.
                assert tree_possible
            else:
                assert not tree_possible
            viable += tree_possible
            files = [prescribed_file(width, history, x) for x in range(1 << width)]
            good = [all(clause & x for clause in history) for x in range(1 << width)]
            if solver:
                for file, verdict in zip(files, good):
                    result = run([solver, '-q'], input=file, capture_output=True, check=False)
                    assert result.returncode == (10 if verdict else 20), result.stderr
            for x in range(1 << width):
                for j in range(width):
                    y = x ^ (1 << j)
                    if x < y:
                        assert sum((a ^ b).bit_count() for a, b in zip(files[x], files[y])) == 1
                        assert len(files[x]) == len(files[y])
                        changes += 1
            minimal = [x for x in range(1 << width) if good[x] and
                       all(not good[x ^ (1 << i)] for i in range(width) if x & (1 << i))]
            assert minimal and all(4 * x.bit_count() >= len(history) for x in minimal)
            tested += len(files)
        print(f'{width} variables: histories {len(histories)}, minimum-zero-cycle cases {viable}, '
              f'pin files {tested}, one-bit adjacencies {changes}')
    # The named first positive obstruction has no allowed two-leaf cut.
    formula = (7, 11, 21)
    for i, j in combinations(range(5), 2):
        assert not fits_two_rectangles(flattening_rows(5, formula, (1 << i) | (1 << j)))

    # Arbitrary clause signs, even inconsistent across occurrences, admit a forward witness.
    tested = 0
    for history in clause_histories(5):
        for signs in product(range(8), repeat=len(history)):
            assignment = 0
            for clause, sign in zip(history, signs):
                variables = [i for i in range(5) if clause & (1 << i)]
                last = variables[-1]
                if not (sign & 4):
                    assignment |= 1 << last
            assert all(any(((assignment >> j) & 1) != ((sign >> k) & 1)
                           for k, j in enumerate(i for i in range(5) if clause & (1 << i)))
                       for clause, sign in zip(history, signs))
            tested += 1
    print(f'{tested} signed five-variable histories have the forward witness')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--solver', help='CaDiCaL executable for independent DIMACS verdict checks')
    run_audit(parser.parse_args().solver)
