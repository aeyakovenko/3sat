"""Check partial transversals and the group-based dense-neighbor SAT solver."""

from collections import Counter, defaultdict
from itertools import combinations, product
from random import Random

from three_valued_defect_choices import holds, reachable_columns


def subsets(seq):
    for size in range(len(seq) + 1):
        yield from combinations(seq, size)


def kernel(edges, size, misses):
    limits = [(size + misses + 1) ** (3 - d) for d in range(4)]
    counts = Counter()
    kept = []
    for edge in edges:
        keys = list(subsets(edge))
        if all(counts[s] < limits[len(s)] for s in keys):
            kept.append(edge)
            counts.update(keys)
    return kept


def patch(edges, size, misses):
    if not edges:
        return set()
    if size:
        for v in edges[0]:
            child = patch([e for e in edges if v not in e], size - 1, misses)
            if child is not None:
                return child | {v}
    if misses:
        return patch(edges[1:], size, misses - 1)
    return None


def link_matching(edges, v):
    matching = []
    used = set()
    for edge in edges:
        if v not in edge:
            continue
        pair = tuple(x for x in edge if x != v)
        if used.isdisjoint(pair):
            matching.append(edge)
            used.update(pair)
    assert all(not used.isdisjoint(set(e) - {v}) for e in edges if v in e)
    return matching, used


def check_kernels():
    edges = list(combinations(range(1, 6), 3))
    tested = 0
    for mask in range(1 << len(edges)):
        family = [e for i, e in enumerate(edges) if mask & (1 << i)]
        for limit, misses in ((1, 0), (1, 1), (2, 0)):
            core = kernel(family, limit, misses)
            t = patch(core, limit, misses)
            oracle = False
            for k in range(limit + 1):
                for chosen in combinations(range(1, 6), k):
                    s = set(chosen)
                    right = sum(s.isdisjoint(e) for e in family) <= misses
                    assert (sum(s.isdisjoint(e) for e in core) <= misses) == right
                    oracle |= right
            assert (t is not None) == oracle
            if t is not None:
                assert sum(t.isdisjoint(e) for e in family) <= misses
            tested += 1
    return tested


def check_tail(rng):
    vertices = range(1, 9)
    candidates = list(combinations(vertices, 3))
    for _ in range(300):
        edges = rng.sample(candidates, rng.randrange(len(candidates) + 1))
        common = set(rng.sample(edges, rng.randrange(len(edges) + 1)))
        t = rng.sample(list(vertices), rng.randrange(1, 9))
        threshold = rng.randrange(1, 5)
        counts = []
        good_count = 0
        for v in t:
            matching, _ = link_matching(edges, v)
            counts.append(len(matching))
            good_count += sum(edge in common for edge in matching) >= threshold
        counts.sort(reverse=True)
        r = len(edges) - len(common)
        assert sum(counts[good_count:]) <= len(t) * threshold + 3 * r
        models = sum(all(any(not z & (1 << (v - 1)) for v in e) for e in common)
                     for z in range(256))
        # Integer version of mu <= 2^(-|J|) + |T| (3/4)^threshold.
        assert (models * (1 << good_count) * (4 ** threshold) <=
                256 * ((4 ** threshold) + (1 << good_count) * len(t) * 3 ** threshold))


def literal_id(t):
    return 2 * (abs(t) - 1) + (t < 0)


def check_group_choice(n, clauses, t, d):
    edges = list(dict.fromkeys(tuple(sorted(map(abs, cl))) for cl in clauses if len(cl) == 3))
    matches = {v: link_matching(edges, v)[1] for v in t}
    places = {}
    for edge in edges:
        for v in edge:
            if v in t:
                places[edge] = v, next(u for u in edge if u != v and u in matches[v])
                break
    for bits in product((0, 1), repeat=len(d)):
        fixed = dict(zip(d, bits))
        base, exceptions = [], []
        pair_groups = defaultdict(list)
        for cl in clauses:
            if any(fixed.get(abs(l)) == (l > 0) for l in cl if abs(l) in fixed):
                continue
            residual = tuple(l for l in cl if abs(l) not in fixed)
            if len(residual) < 3:
                base.append(residual)
                continue
            where = places.get(tuple(sorted(map(abs, residual))))
            if where is None:
                exceptions.append(residual)
                continue
            p, q = where
            left = next(l for l in residual if abs(l) == p)
            right = next(l for l in residual if abs(l) == q)
            third = next(l for l in residual if abs(l) not in where)
            pair_groups[left, right].append(third)
        reach = reachable_columns(n, base)
        if reach is None:
            continue
        x_vars = sorted({abs(l) for sign_pair in pair_groups for l in sign_pair})
        groups = list(pair_groups.values())
        groups += [(v,) for v in range(1, n + 1)] + [(-v,) for v in range(1, n + 1)]
        units = {g[0]: i for i, g in enumerate(groups) if len(g) == 1}
        # Independent truth-table audit of the word-propagated group conflicts.
        conflicts = []
        for lhs in groups:
            row = set()
            for j, rhs in enumerate(groups):
                if any(reach[literal_id(a)] & (1 << (literal_id(b) ^ 1))
                       for a in lhs for b in rhs):
                    row.add(j)
            conflicts.append(row)
        for x_bits in product((0, 1), repeat=len(x_vars)):
            x = dict(zip(x_vars, x_bits))
            active = {units[v if value else -v] for v, value in x.items()}
            for j, (l, r) in enumerate(pair_groups):
                if not (x[abs(l)] == (l > 0) or x[abs(r)] == (r > 0)):
                    active.add(j)
            for choice in product(*exceptions):
                bundle = active | {units[l] for l in choice}
                if all(conflicts[i].isdisjoint(bundle) for i in bundle):
                    return True
    return False


def check_solver(rng):
    results = Counter()
    for i in range(130):
        n = rng.randrange(3, 8)
        clauses = [tuple(v if rng.randrange(2) else -v for v in
                         rng.sample(range(1, n + 1), rng.choice([1, 2, 3, 3, 3])))
                   for _ in range(rng.randrange(5, 20))]
        if i % 7 == 0:
            clauses += [tuple(v if b else -v for v, b in enumerate(bits, 1))
                        for bits in product((0, 1), repeat=3)]
        t = rng.sample(list(range(1, n + 1)), rng.randrange(n + 1))
        d = rng.sample(t, rng.randrange(len(t) + 1))
        observed = check_group_choice(n, clauses, t, d)
        actual = any(holds(clauses, z) for z in range(1 << n))
        assert observed == actual
        results[actual] += 1
    return results


if __name__ == '__main__':
    rng = Random(55861)
    checked = check_kernels()
    check_tail(rng)
    counts = check_solver(rng)
    print(f'{checked} partial kernel budgets, 300 tail and density checks, '
          f'{counts[True]} SAT and {counts[False]} UNSAT grouped files')
