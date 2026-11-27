"""Exhaust short SAT interfaces, deterministic cell probes, and witnessed probes."""

from argparse import ArgumentParser
from functools import lru_cache
from itertools import product
from math import comb
from subprocess import run


def deterministic_depths(bits):
    databases = 1 << bits
    full = (1 << databases) - 1
    intersections = [sum(1 << a for a in range(databases) if a & b) for b in range(databases)]
    tests = [intersections[1 << i] for i in range(bits)]
    worst = bytearray(full + 1)
    for query in intersections:
        depth = bytearray(full + 1)
        for family in range(1, full + 1):
            if (family & query) in (0, family):
                continue
            best = bits
            for test in tests:
                part = family & test
                if part not in (0, family):
                    best = min(best, 1 + max(depth[part], depth[family ^ part]))
            depth[family] = best
            worst[family] = max(worst[family], best)
    return worst


def witnessed_classes(bits, probes):
    databases = 1 << bits
    full = (1 << databases) - 1
    probe_sets = [s for s in range(databases) if s.bit_count() == probes]
    safe_for = []
    for a in range(databases):
        rivals = [b for b in range(databases) if b & ~a]
        # A certificate succeeds on a if no rival in this class agrees on the tested cells.
        forbidden = [sum(1 << b for b in rivals if not ((a ^ b) & s)) for s in probe_sets]
        safe_for.append(bytearray(any(not (family & f) for f in forbidden) for family in range(full + 1)))
    admissible = bytearray(full + 1)
    for family in range(full + 1):
        remaining = family
        while remaining:
            bit = remaining & -remaining
            if not safe_for[bit.bit_length() - 1][family]:
                break
            remaining ^= bit
        else:
            admissible[family] = 1
    return admissible


def class_cover(admissible, databases):
    full = len(admissible) - 1
    maximal = [c for c in range(1, full + 1) if admissible[c] and
               all((c >> a) & 1 or not admissible[c | (1 << a)] for a in range(databases))]
    containing = [[c for c in maximal if (c >> a) & 1] for a in range(databases)]

    @lru_cache(None)
    def cover(remaining):
        if not remaining:
            return 0
        a = (remaining & -remaining).bit_length() - 1
        return 1 + min(cover(remaining & ~c) for c in containing[a])

    return cover(full), max(c.bit_count() for c in maximal), len(maximal)


def audit_probes():
    expected = {1: (2, 1), 2: (4, 2, 1), 3: (8, 3, 2, 1), 4: (16, 4, 2, 2, 1)}
    for bits, counts in expected.items():
        databases = 1 << bits
        worst = deterministic_depths(bits)
        for probes, count in enumerate(counts):
            deterministic = bytearray(d <= probes for d in worst)
            witness = witnessed_classes(bits, probes)
            d_count, d_max, d_classes = class_cover(deterministic, databases)
            w_count, w_max, w_classes = class_cover(witness, databases)
            assert d_count == w_count == count
            assert d_max == w_max == sum(comb(bits, i) for i in range(probes + 1))
            assert all(not d or w for d, w in zip(deterministic, witness))
            print(f'm={bits}, t={probes}: {count} messages, capacity {d_max}, '
                  f'{d_classes} maximal deterministic / {w_classes} maximal witnessed classes')


def lookup_formula(a, b):
    # Address bits 1,2 are shared. Each side has one private padding variable.
    clauses = []
    for table, pad in ((a, 3), (b, 4)):
        for j in range(4):
            if not (table >> j) & 1:
                reject = tuple(-var if (j >> (var - 1)) & 1 else var for var in (1, 2))
                clauses.extend([(*reject, pad), (*reject, -pad)])
    return clauses


def pin_false_triple(pads):
    return [tuple(-p if (j >> i) & 1 else p for i, p in enumerate(pads)) for j in range(1, 8)]


def tagged_formula(a, b, intersection):
    # Shared words 5..8 give the whole database. Names 2,3 are complementary tag variables.
    left_pads = (9, 10, 11)
    right_pads = (12, 13, 14)
    clauses = pin_false_triple(left_pads) + pin_false_triple(right_pads)
    clauses.extend(((5 + j) if (a >> j) & 1 else -(5 + j), *left_pads[:2]) for j in range(4))
    clauses.extend([(2, 3, right_pads[0]), (-2, -3, right_pads[0])])
    selected = [5 + j for j in range(4) if (b >> j) & 1]
    clauses.extend((2, -z, right_pads[0]) for z in selected)
    row = [-2, *selected]
    next_fresh = 15
    while len(row) > 3:
        clauses.append((row[0], row[1], next_fresh))
        row = [-next_fresh, *row[2:]]
        next_fresh += 1
    clauses.append(tuple(row + list(right_pads[:3-len(row)])))
    clauses.append((2 if intersection else 3, *right_pads[:2]))
    return clauses, next_fresh


def evaluate(clauses, ones):
    return all(any((abs(literal) in ones) == (literal > 0) for literal in clause) for clause in clauses)


def dimacs(clauses, largest):
    assert all(len(clause) == len({abs(literal) for literal in clause}) == 3 for clause in clauses)
    rows = [f'p cnf {largest} {len(clauses)}', *(' '.join(map(str, clause)) + ' 0' for clause in clauses)]
    return ('\n'.join(rows) + '\n').encode('ascii')


def check_solver(solver, data, expected):
    if solver:
        proc = run([solver], input=data, capture_output=True, check=False)
        assert proc.returncode == (10 if expected else 20), proc.returncode


def audit_sat(solver):
    for a, b in product(range(16), repeat=2):
        clauses = lookup_formula(a, b)
        actual = any(evaluate(clauses, {i + 1 for i in range(4) if (raw >> i) & 1}) for raw in range(16))
        assert actual == bool(a & b)
        check_solver(solver, dimacs(clauses, 4), actual)
        files = []
        for tag in (False, True):
            rows, fresh = tagged_formula(a, b, tag)
            forced = {5 + i for i in range(4) if (a >> i) & 1} | {2 if tag else 3}
            actual = any(evaluate(rows, forced | {15 + i for i in range(fresh - 15) if (v >> i) & 1})
                         for v in range(1 << (fresh - 15)))
            assert actual == (bool(a & b) == tag)
            files.append(dimacs(rows, fresh - 1))
            check_solver(solver, files[-1], actual)
        assert len(files[0]) == len(files[1])
        assert sum((x ^ y).bit_count() for x, y in zip(*files)) == 1
    print('256 untagged proper files, 256 tagged pairs at physical Hamming distance one')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--solver', help='independent DIMACS solver on stdin with verdict exit codes 10 and 20')
    audit_sat(parser.parse_args().solver)
    audit_probes()
