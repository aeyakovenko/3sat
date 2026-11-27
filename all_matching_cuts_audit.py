"""Check constant-time singleton edit queries and compile subformula selection into matching cuts."""

import argparse
from collections import defaultdict
from itertools import permutations, product
from random import Random

from bounded_relay_sheet_audit import inverse
from sheet_guard_deletions_audit import (
    CLAUSE_DELETIONS,
    INTACT,
    brute_sat,
    local_clauses,
    serialize_dimacs,
    solve_dimacs,
)


class SingleCutIndex:
    def __init__(self, p, q):
        self.q = q
        self.previous = inverse(q)
        back = inverse(p)
        self.mate = tau = [back[j] for j in q]
        assert all(tau[j] == i for i, j in enumerate(tau))
        self.cycle = [-1] * len(q)
        self.pos = [0] * len(q)
        self.ranks = []
        for root in range(len(q)):
            if self.cycle[root] != -1:
                continue
            ranks = [0]
            v = root
            while self.cycle[v] == -1:
                self.cycle[v] = len(self.ranks)
                self.pos[v] = len(ranks) - 1
                viable = {v, tau[v]}.isdisjoint({q[v], q[tau[v]]})
                ranks.append(ranks[-1] + int(viable))
                v = q[v]
            self.ranks.append(ranks)

    def verdict(self, u):
        q, tau = self.q, self.mate
        v = tau[u]
        if self.cycle[u] != self.cycle[v]:
            return True
        if {u, q[u]} & {v, q[v]}:
            return False
        cycle = self.cycle[u]
        rank = self.ranks[cycle]
        left, right = self.pos[q[u]], self.pos[v]
        count = rank[right] - rank[left] + (rank[-1] if right < left else 0)
        forbidden = {self.previous[u], u, v, q[v]}
        for i in forbidden | {tau[z] for z in forbidden}:
            if self.cycle[i] != cycle:
                continue
            j = self.pos[i]
            inside = left <= j < right if left <= right else (j >= left or j < right)
            if inside:
                count -= rank[j + 1] - rank[j]
        return count > 0


def test_census(n):
    perms = list(permutations(range(n)))
    involutions = [m for m in perms if all(m[m[j]] == j for j in range(n))]
    ones = [sum(1 << s for s in range(1 << n) if (s >> i) & 1) for i in range(n)]
    universe = (1 << (1 << n)) - 1
    zeros = [x ^ universe for x in ones]
    count = yes = 0
    for p in perms:
        inverse_p = inverse(p)
        for tau in involutions:
            q = [p[j] for j in tau]
            inverse_q = inverse(q)
            index = SingleCutIndex(p, q)
            for cut, right in enumerate(p):
                # Direct projected local tests at every left and right center.
                states = universe
                for i in range(n):
                    if i == cut:
                        states &= ones[i] & ones[q[i]]
                    else:
                        states &= zeros[i] | zeros[p[i]] | ones[q[i]]
                    if i == right:
                        states &= zeros[i] & zeros[inverse_q[i]]
                    else:
                        states &= ones[i] | ones[inverse_p[i]] | zeros[inverse_q[i]]
                assert index.verdict(cut) == bool(states)
                yes += bool(states)
                count += 1
    return count, yes


class BatchCutIndex:
    """Reference kernel with enumeration of representatives at its last step."""

    def __init__(self, rho, p, q):
        self.p, self.q = p, q
        self.back_q = inverse(q)
        back = inverse(p)
        self.tau = tau = [back[i] for i in q]
        self.back_tau = inverse(tau)
        self.first = [(i, j) for i, j in enumerate(rho) if i != j]
        self.long = [i for i, j in enumerate(tau) if tau[j] != i]
        self.marks = {v for pair in self.first for v in pair} | set(self.long) | {q[i] for i in self.long}
        self.cycle = [-1] * len(q)
        self.pos = [0] * len(q)
        self.rows = []
        for root in range(len(q)):
            if self.cycle[root] >= 0:
                continue
            rank, select = [0], []
            i = root
            while self.cycle[i] < 0:
                self.cycle[i] = len(self.rows)
                self.pos[i] = len(rank) - 1
                if tau[tau[i]] == i and {i, tau[i]}.isdisjoint({q[i], q[tau[i]]}):
                    select.append(i)
                rank.append(len(select))
                i = q[i]
            self.rows.append((rank, select))

    def verdict(self, cuts):
        q, tau = self.q, self.tau
        ones = set(cuts) | {q[i] for i in cuts}
        zeros = {self.p[i] for i in cuts} | {self.back_q[self.p[i]] for i in cuts}
        if not ones.isdisjoint(zeros):
            return False
        extra = sorted(self.marks - ones - zeros)
        groups = defaultdict(list)
        for v in sorted(ones | zeros | self.marks, key=lambda i: (self.cycle[i], self.pos[i])):
            groups[self.cycle[v]].append(v)
        arcs = [(v, group[(j + 1) % len(group)]) for group in groups.values() for j, v in enumerate(group)]

        def inside(i, left, right):
            if self.cycle[i] != self.cycle[left]:
                return False
            x, y, z = self.pos[i], self.pos[left], self.pos[right]
            return y <= x < z if y < z else x >= y or x < z

        for assignment in product((False, True), repeat=len(extra)):
            values = {**dict.fromkeys(ones, True), **dict.fromkeys(zeros, False), **dict(zip(extra, assignment))}
            if any(values[i] != values[j] for i, j in self.first):
                continue
            fixed = [i for i in self.long if values[i] and not values[q[i]]]
            if any(not values[tau[i]] or values[q[self.back_tau[i]]] for i in fixed):
                continue
            missing = [(lft, rgt) for lft, rgt in arcs
                       if values[lft] and not values[rgt] and not any(inside(i, lft, rgt) for i in fixed)]
            if not missing:
                return True
            options = []
            for left, right in missing:
                rank, select = self.rows[self.cycle[left]]
                a, b = self.pos[left], self.pos[right]
                i, j = rank[a], rank[b]
                length = j - i + (len(select) if b < a else 0)
                cap = 4 * (len(missing) - 1) + 1
                candidates = set()
                for offset in range(min(length, 2 * (2 * len(values) + cap))):
                    z = select[(i + offset) % len(select)]
                    y = tau[z]
                    if all(values.get(v, True) and not values.get(q[v], False) for v in (z, y)):
                        candidates.add(min(z, y))
                        if len(candidates) == cap:
                            break
                options.append(candidates)
            for choice in product(*options):
                descent = set(choice) | {tau[c] for c in choice} | set(fixed)
                if descent.isdisjoint(q[i] for i in descent):
                    return True
        return False


def test_batch_census(n):
    perms = list(permutations(range(n)))
    ones = [sum(1 << s for s in range(1 << n) if s >> i & 1) for i in range(n)]
    universe = (1 << (1 << n)) - 1
    zeros = [universe ^ s for s in ones]
    count = yes = 0
    for rho, p, q in product(perms, repeat=3):
        index = BatchCutIndex(rho, p, q)
        pinv, qinv = inverse(p), inverse(q)
        first = universe
        for i, j in enumerate(rho):
            first &= universe ^ (ones[i] ^ ones[j])
        for s in range(1 << n):
            cuts = {i for i in range(n) if s >> i & 1}
            states = first
            for i in range(n):
                states &= (ones[i] & ones[q[i]]) if i in cuts else (zeros[i] | zeros[p[i]] | ones[q[i]])
                states &= ((zeros[i] & zeros[qinv[i]]) if pinv[i] in cuts
                           else (ones[i] | ones[pinv[i]] | zeros[qinv[i]]))
            assert index.verdict(cuts) == bool(states)
            count += 1
            yes += bool(states)
    return count, yes


def test_mixed_queries():
    rng = Random(84013)
    count = yes = 0
    for n in (8, 10, 12):
        ones = [sum(1 << s for s in range(1 << n) if s >> i & 1) for i in range(n)]
        universe = (1 << (1 << n)) - 1
        zeros = [universe ^ x for x in ones]
        for _ in range(150):
            order = rng.sample(range(n), n)
            rho = list(range(n))
            if rng.randrange(2):
                i, j = order[:2]
                rho[i], rho[j] = j, i
            tau = list(range(n))
            start = 0
            if rng.randrange(2):
                chain = order[:3]
                for i, j in zip(chain, chain[1:] + chain[:1]):
                    tau[i] = j
                start = 3
            for i, j in zip(order[start::2], order[start + 1::2]):
                tau[i], tau[j] = j, i
            p = rng.sample(range(n), n)
            q = [p[i] for i in tau]
            pinv, qinv = inverse(p), inverse(q)
            index = BatchCutIndex(rho, p, q)
            for size in range(1, 5):
                cuts = set(rng.sample(range(n), size))
                states = universe
                for i, j in enumerate(rho):
                    states &= universe ^ (ones[i] ^ ones[j])
                    states &= (ones[i] & ones[q[i]]) if i in cuts else (zeros[i] | zeros[p[i]] | ones[q[i]])
                    states &= ((zeros[i] & zeros[qinv[i]]) if pinv[i] in cuts
                               else (ones[i] | ones[pinv[i]] | zeros[qinv[i]]))
                assert index.verdict(cuts) == bool(states)
                count += 1
                yes += bool(states)
    return count, yes


def clone_occurrences(rows):
    groups = defaultdict(list)
    bounded, next_name = [], 1
    for row in rows:
        fresh_row = []
        for literal in row:
            groups[abs(literal)].append(next_name)
            fresh_row.append(next_name if literal > 0 else -next_name)
            next_name += 1
        bounded.append(tuple(fresh_row))
    for group in groups.values():
        if len(group) > 1:
            bounded.extend((-v, group[(i + 1) % len(group)]) for i, v in enumerate(group))
    return bounded, next_name - 1


def compile_layout(rows, variables):
    q = []
    tau = []

    def cycle(size):
        start = len(q)
        result = list(range(start, start + size))
        q.extend(result[1:] + result[:1])
        tau.extend([-1] * size)
        return result

    def pair(i, j):
        assert i != j and tau[i] == tau[j] == -1
        tau[i], tau[j] = j, i

    unused = {}
    for x in range(1, variables + 1):
        p0, n0, p1, n1 = cycle(4)
        unused[x], unused[-x] = [p0, p1], [n0, n1]
    cuts = []
    for row in rows:
        assert 1 <= len(row) <= 3
        u, c1, c2, c3, v, _ = cycle(6)
        cuts.append(u)
        pair(u, v)
        for pos, literal in zip((c1, c2, c3), row):
            pair(pos, unused[literal].pop())
    for i in range(len(tau)):
        if tau[i] == -1:
            pair(i, cycle(1)[0])
    p = [q[j] for j in tau]
    assert sorted(p) == sorted(q) == list(range(len(q)))
    assert all(tau[j] == i and i != j for i, j in enumerate(tau))
    return p, q, cuts


def file_for_edits(p, q, anchors, applied):
    n = len(p)
    inv_p, inv_q = inverse(p), inverse(q)
    centers = {(0, u) for u in anchors} | {(1, p[u]) for u in anchors}
    changed = {(0, u) for u in applied} | {(1, p[u]) for u in applied}
    a_names, b_names = {}, {}
    for j, u in enumerate(anchors):
        a_names[u], b_names[p[u]] = 10 * j + 2, 10 * j + 3
    blocked = set(a_names.values()) | set(b_names.values())
    fresh = (i for i in range(1, 10 * n + 1) if i not in blocked)
    for mapping in (a_names, b_names):
        for i in range(n):
            if i not in mapping:
                mapping[i] = next(fresh)
    rows = []
    for layer, side, i in product((0, 1), (0, 1), range(n)):
        own, other = (b_names, a_names) if side else (a_names, b_names)
        center = own[i]
        a = b = other[i]
        guard = INTACT
        if layer:
            a = center if (side, i) in changed else other[(inv_p if side else p)[i]]
            b = other[(inv_q if side else q)[i]]
            guard = INTACT if (side, i) in centers else CLAUSE_DELETIONS
        rows.extend(local_clauses(center, a, b, next(fresh), next(fresh), guard))
    assert all(len({abs(x) for x in row}) == 3 for row in rows)
    return serialize_dimacs(10 * n, rows)


def selection_tests(solver):
    # All source-clause masks share one fixed matching even before any source
    # clause is selected. The directed cycle-of-copies clauses stay selected.
    base = list(product((-1, 1), (-2, 2), (-3, 3)))
    rng = Random(70231)
    source_hosts = [base]
    for n in (4, 5, 6):
        source_hosts.append([tuple(rng.choice((-1, 1)) * v for v in rng.sample(range(1, n + 1), 3))
                             for _ in range(6 * n)])
    # A minimally unsatisfiable full decision tree exercises a second variable pattern.
    tree = []
    for state in product((0, 1), repeat=3):
        row, node = [], 1
        for b in state:
            row.append(-node if b else node)
            node = 2 * node + b
        tree.append(tuple(row))
    source_hosts.append(tree)
    count = no = 0
    for original in source_hosts:
        rows, variables = clone_occurrences(original)
        p, q, anchors = compile_layout(rows, variables)
        always = anchors[len(original):]
        base_data = file_for_edits(p, q, anchors, always)
        if len(original) <= 8:
            masks = range(1 << len(original))
        else:
            masks = [0, (1 << len(original)) - 1, *(rng.getrandbits(len(original)) for _ in range(18))]
        for bits in masks:
            chosen = [i for i in range(len(original)) if bits >> i & 1]
            expected = brute_sat(max(abs(x) for row in original for x in row), [original[i] for i in chosen])
            data = file_for_edits(p, q, anchors, [*always, *(anchors[i] for i in chosen)])
            assert len(data) == len(base_data)
            assert sum((a ^ b).bit_count() for a, b in zip(data, base_data)) == 2 * len(chosen)
            assert solve_dimacs(solver, data) == expected
            count += 1
            no += not expected
    return count, no


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', help='also test subformula selection on raw files using a DIMACS solver')
    args = parser.parse_args()
    for n in range(1, 7):
        print(f'{n} positions: {test_census(n)} (cut queries, SAT)', flush=True)
    for n in range(1, 5):
        print(f'{n} positions: {test_batch_census(n)} (all cut-set queries, SAT)', flush=True)
    print('mixed cut-set queries and SAT:', test_mixed_queries(), flush=True)
    if args.solver:
        print('subformula files, UNSAT:', selection_tests(args.solver))
