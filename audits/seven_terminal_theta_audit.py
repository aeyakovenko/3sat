"""Check the remaining cycle-rank-two networks for a seven-variable proper CNF.

Usage: python seven_terminal_theta_audit.py /path/to/cadical
Requires NumPy and an LRAT-capable CaDiCaL. Each UNSAT certificate is checked
by the separate unit-propagation implementation below.
"""

import argparse
import itertools
import subprocess
import tempfile
from pathlib import Path

import numpy as np

CLAUSES = (7, 11, 28, 49, 100)
TRIPLE = (2, 5, 6)


def spread(compact, positions):
    return sum(((compact >> k) & 1) << position for k, position in enumerate(positions))


def columns(inside):
    """One mask on inside assignments for every outside assignment."""
    outside = tuple(i for i in range(7) if i not in inside)
    result = []
    for right in range(1 << len(outside)):
        fixed = spread(right, outside)
        mask = 0
        for left in range(1 << len(inside)):
            point = spread(left, inside) | fixed
            if all(clause & point for clause in CLAUSES):
                mask |= 1 << left
        result.append(mask)
    return result


def has_fooling_set(cols, size):
    cells = [(r, c) for c, column in enumerate(cols) for r in range(column.bit_length())
             if (column >> r) & 1]

    def search(candidates, target):
        if target == 0:
            return True
        if len(candidates) < target:
            return False
        for i, (r, c) in enumerate(candidates):
            compatible = [(s, d) for s, d in candidates[i + 1:]
                          if not ((cols[c] >> s) & (cols[d] >> r) & 1)]
            if search(compatible, target - 1):
                return True
        return False

    return search(cells, size)


def gate(lane, code):
    """Four eight-bit truth tables in row-major endpoint order."""
    return tuple(sum(((code >> (entry + 4 * ((t >> lane) & 1))) & 1) << t
                     for t in range(8)) for entry in range(4))


def multiply(a, b):
    return (a[0] & b[0] | a[1] & b[2], a[0] & b[1] | a[1] & b[3],
            a[2] & b[0] | a[3] & b[2], a[2] & b[1] | a[3] & b[3])


def canonical(signature):
    transforms = []
    for flip in range(4):
        for transpose in (False, True):
            remap = [(i % 2) * 2 + i // 2 if transpose else i for i in range(4)]
            transforms.append(tuple(signature[i ^ flip] for i in remap))
    return min(transforms)


def path_signatures(target):
    pools = [[gate(i, j) for j in range(256)] for i in range(3)]
    found = set()
    counts = []
    for a, b, c in itertools.permutations(range(3)):
        # Exact deduplication after two sites. NumPy evaluates the same product
        # on many candidates in parallel; bitwise AND/OR compose relations.
        two_sites = sorted({multiply(x, y) for x in pools[a] for y in pools[b]})
        two_sites = np.asarray(two_sites, dtype=np.uint8).T
        order_signatures = set()
        for final in pools[c]:
            product = np.stack(multiply(two_sites, final), axis=1)
            live = np.ones(len(product), dtype=bool)
            for column in sorted(set(target) - {0}):
                subset = (product & column) == product
                union = np.bitwise_or.reduce(np.where(subset, product, 0), axis=1)
                live &= union == column
            order_signatures.update(map(tuple, product[live].tolist()))
        counts.append(len(order_signatures))
        found.update(order_signatures)
    assert counts == [0, 288, 0, 288, 0, 0] and len(found) == 576
    return sorted({canonical(f) for f in found})


class Clauses:
    def __init__(self):
        self.count = 0
        self.rows = []

    def variable(self):
        self.count += 1
        return self.count

    def conjunction(self, entries):
        entries = list(entries)
        out = self.variable()
        self.rows.extend((-out, e) for e in entries)
        self.rows.append((out, *(-e for e in entries)))
        return out

    def disjunction(self, entries):
        # De Morgan allows an output literal of either sign.
        return -self.conjunction(-e for e in entries)

    def write(self, path):
        with path.open('w') as stream:
            print(f'p cnf {self.count} {len(self.rows)}', file=stream)
            for row in self.rows:
                print(*row, 0, file=stream)


def theta(ordered, signatures, target):
    """Synthesize a pair of hubs and four remaining pin tables."""
    cnf = Clauses()
    hubs = [[cnf.variable() for _ in range(8)] for _ in range(2)]
    sites = [[cnf.variable() for _ in range(8)] for _ in range(4)]
    quadruples = list(itertools.product(range(2), repeat=4))
    # k = 2 * left_end + right_end, consistent with the long path's rows.
    joint_hub = [[cnf.conjunction((hubs[0][(k >> 1) | (i << 1) | (j << 2)],
                                   hubs[1][(k & 1) | (u << 1) | (v << 2)]))
                  for i, j, u, v in quadruples] for k in range(4)]

    def short_path(pair):
        left, right = sites[2 * pair:2 * pair + 2]
        out = {}
        for a, b, i, j in quadruples:
            bridges = (cnf.conjunction((left[i | (s << 1) | (a << 2)],
                                        right[s | (j << 1) | (b << 2)])) for s in range(2))
            out[a, b, i, j] = cnf.disjunction(bridges)
        return out

    first, second = short_path(0), short_path(1)
    outside = []
    for z in range(16):
        a, b, c, d = [(z >> lane) & 1 for lane in ordered]
        joint_path = [cnf.conjunction((first[a, b, i, u], second[c, d, j, v]))
                      for i, j, u, v in quadruples]
        outside.append([cnf.disjunction(cnf.conjunction((r, h))
                                        for r, h in zip(joint_path, joint_hub[k]))
                        for k in range(4)])

    choice = []
    for signature in signatures:
        select = cnf.variable()
        choice.append(select)
        for exits, column in zip(outside, target):
            for k, mask in enumerate(signature):
                if mask & ~column:
                    cnf.rows.append((-select, -exits[k]))
            for t in range(8):
                if (column >> t) & 1:
                    cnf.rows.append((-select, *(exits[k] for k, mask in enumerate(signature)
                                                if (mask >> t) & 1)))
    cnf.rows.append(tuple(choice))
    return cnf, hubs, sites


def checked_refutation(clauses, path):
    """Validate each addition by its positive LRAT unit-propagation hints."""
    db = dict(enumerate(clauses, 1))
    last = len(clauses)
    with path.open() as stream:
        for line in stream:
            tokens = line.split()
            if tokens[1] == 'd':
                continue  # Retaining proven clauses preserves logical implication.
            row = list(map(int, tokens))
            number = row[0]
            zero = row.index(0, 1)
            clause, hints = row[1:zero], row[zero + 1:-1]
            assert number > last and row[-1] == 0 and all(i > 0 for i in hints)
            last = number
            trail = {-lit for lit in clause}
            conflict = any(lit in trail for lit in clause)
            for hint in hints:
                if conflict:
                    break
                possible = {lit for lit in db[hint] if -lit not in trail}
                assert not possible.intersection(trail)
                if possible:
                    assert len(possible) == 1
                    trail.update(possible)
                else:
                    conflict = True
            assert conflict
            db[number] = clause
            if not clause:
                return
    raise ValueError('refutation did not derive an empty clause')


def native_column(order, outside, signature, tables):
    """Independent enumeration of all eight remaining edge bits."""
    hub_a, hub_b, site_a, site_b, site_c, site_d = tables
    a, b, c, d = [(outside >> lane) & 1 for lane in order]
    column = 0
    for x, y, i, j, u, v, p, q in itertools.product(range(2), repeat=8):
        points = (x | (i << 1) | (j << 2), y | (u << 1) | (v << 2),
                  i | (p << 1) | (a << 2), p | (u << 1) | (b << 2),
                  j | (q << 1) | (c << 2), q | (v << 1) | (d << 2))
        if all((table >> pin) & 1 for table, pin in zip((hub_a, hub_b, site_a, site_b, site_c, site_d), points)):
            column |= signature[2 * x + y]
    return column


def run(solver):
    assert all(has_fooling_set(columns(pair), 3) for pair in itertools.combinations(range(7), 2))
    allowed = [triple for triple in itertools.combinations(range(7), 3)
               if not has_fooling_set(columns(triple), 5)]
    assert allowed == [TRIPLE]
    target = columns(TRIPLE)
    signatures = path_signatures(target)
    assert len(signatures) == 72
    with tempfile.TemporaryDirectory() as folder:
        formula = Path(folder) / 'search.cnf'
        proof = Path(folder) / 'search.lrat'
        # Positive control uses fixed known gates, checked against a direct
        # enumeration rather than the synthesis circuit's evaluation rules.
        order = (2, 0, 3, 1)
        tables = (102, 228, 22, 244, 185, 58)
        expected = [native_column(order, z, signatures[0], tables) for z in range(16)]
        assert len(set(expected)) >= 3
        trial, hubs, sites = theta(order, [signatures[0]], expected)
        for variables, table in zip(hubs + sites, tables):
            trial.rows.extend((v if (table >> i) & 1 else -v,) for i, v in enumerate(variables))
        trial.write(formula)
        assert subprocess.run([solver, '-q', str(formula)], check=False, capture_output=True).returncode == 10
        tested = 0
        for order in itertools.permutations(range(4)):
            if order[0] > order[2]:
                continue  # Exchange the two unlabeled short paths.
            problem, _, _ = theta(order, signatures, target)
            problem.write(formula)
            proof.unlink(missing_ok=True)
            result = subprocess.run([solver, '-q', '--plain', '--lrat', '--no-binary',
                                     str(formula), str(proof)], check=False, capture_output=True)
            assert result.returncode == 20, (order, result.stdout, result.stderr)
            checked_refutation(problem.rows, proof)
            tested += 1
    assert tested == 12
    print('All 21 pair cuts and 34 triple cuts have fooling sets.')
    print('576 three-site signatures give 72 classes; all 12 theta refutations verified.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cadical', help='LRAT-capable CaDiCaL executable')
    run(parser.parse_args().cadical)
