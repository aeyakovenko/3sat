"""Audit the parity/clause component claim and the signed split counterexample."""
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, product
from random import Random


def row_library(n):
    """Return (variable mask, bitset of assignments failing the row)."""
    rows = []
    for support in range(1 << n):
        for charge in (0, 1):
            if not support and not charge:
                continue
            bad = sum(1 << x for x in range(1 << n)
                      if (x & support).bit_count() % 2 != charge)
            rows.append((support, bad))
    for i, j in combinations(range(n), 2):
        support = (1 << i) | (1 << j)
        for left, right in product((0, 1), repeat=2):
            bad = sum(1 << x for x in range(1 << n)
                      if x & support == (left << i) | (right << j))
            rows.append((support, bad))
    return rows


def check_component(n, rows):
    # Keep components with all variable occurrences at most two.
    seen = twice = 0
    for support, _ in rows:
        if twice & support:
            return False, False
        twice |= seen & support
        seen |= support
    reached = rows[0][0]
    for _ in rows:
        for support, _ in rows:
            if support & reached:
                reached |= support
    if any(support & ~reached or (len(rows) > 1 and not support)
           for support, _ in rows):
        return False, False

    universe = (1 << (1 << n)) - 1
    rejected = 0
    for _, bad in rows:
        rejected |= bad
    if rejected != universe:
        return True, False
    for chosen in range(len(rows)):
        other_bad = 0
        for i, (_, bad) in enumerate(rows):
            if i != chosen:
                other_bad |= bad
        assert rows[chosen][1] & ~other_bad
    return True, True


def run_components():
    total = incompatible = 0
    library = row_library(3)
    for count in range(1, 6):
        for rows in combinations_with_replacement(library, count):
            connected, unsat = check_component(3, rows)
            total += connected
            incompatible += unsat
    rng = Random(3802)
    library = row_library(5)
    for _ in range(25000):
        rows = rng.choices(library, k=rng.randrange(2, 7))
        connected, unsat = check_component(5, rows)
        total += connected
        incompatible += unsat
    return total, incompatible


def bin_costs():
    # Tree ((x0,x1),(x2,x3)) on one side and (x4,x5) on the other.
    costs = []
    for leaves in range(64):
        children = [(leaves >> j) & 1 for j in range(6)]
        best = 6
        for labels in product((0, 1), repeat=5):
            a, b, c, d, root = labels
            errors = sum((children[0] + children[1] != a,
                          children[2] + children[3] != b,
                          children[4] + children[5] != c,
                          a + b != d, d + c != root))
            assert sum(children) <= root + 2 * errors
            best = min(best, errors)
        assert (best == 0) == (leaves.bit_count() <= 1)
        costs.append(best)
    return costs


def check_split_instance():
    # Six left vertices with all three right vertices available at each.
    costs = bin_costs()
    minimum = 22
    for a, b, c in product(range(64), repeat=3):
        single = (a & ~b & ~c) | (b & ~a & ~c) | (c & ~a & ~b)
        failed_demands = 6 - single.bit_count()
        errors = failed_demands + costs[a] + costs[b] + costs[c]
        assert 2 * errors >= 3
        minimum = min(minimum, errors)
    for selected in combinations(range(6), 3):
        bins = tuple(1 << left for left in selected)
        assert all(costs[marks] == 0 for marks in bins)
        assert all(sum((marks >> left) & 1 for marks in bins) == 1
                   for left in selected)
    return minimum


def matching_defects(rows):
    # Ports and wire nodes have separate integer names in each mirror copy.
    base = []
    optional = set()
    ports = {}

    def vertex(free=False):
        v = len(base)
        base.append(set())
        if free:
            optional.add(v)
        return v

    def join(v, w):
        base[v].add(w)
        base[w].add(v)

    for kind, literals in rows:
        terminals = []
        for name, sign in literals:
            v = vertex()
            ports.setdefault(name, []).append((v, sign))
            terminals.append(v)
        q = len(terminals)
        if kind in ("odd", "even"):
            if q % 2 != (kind == "odd"):
                terminals.append(vertex())
            for v, w in combinations(terminals, 2):
                join(v, w)
        else:
            internal = [vertex() for _ in range(q - 1)]
            if kind == "atmost":
                internal.append(vertex(free=True))
            for v, w in product(terminals, internal):
                join(v, w)
    for occurrences in ports.values():
        if len(occurrences) == 1:
            join(occurrences[0][0], vertex(free=True))
        else:
            (a, s), (b, t) = occurrences
            if s == t:
                join(a, b)
            else:
                mid = vertex()
                join(a, mid)
                join(b, mid)

    n = len(base)
    adj = [sum(1 << w for w in nb) for nb in base]
    adj += [mask << n for mask in adj]
    for v in optional:
        adj[v] |= 1 << (v + n)
        adj[v+n] |= 1 << v

    @lru_cache(None)
    def unmatched(mask):
        if not mask:
            return 0
        v = min((i for i in range(2*n) if mask >> i & 1),
                key=lambda i: (adj[i] & mask).bit_count())
        rest = mask ^ (1 << v)
        neighbors = adj[v] & rest
        best = 1 + unmatched(rest)
        while neighbors and best:
            w = neighbors & -neighbors
            neighbors ^= w
            best = min(best, unmatched(rest ^ w))
        return best

    return unmatched((1 << (2*n)) - 1)


def test_matching_reduction():
    rng = Random(88)
    positive = 0
    for _ in range(240):
        n = rng.randrange(2, 5)
        remaining = [2] * n
        rows = []
        for _ in range(rng.randrange(2, 6)):
            usable = [v for v, cap in enumerate(remaining) if cap]
            if not usable:
                break
            variables = rng.sample(usable, rng.randrange(1, min(len(usable), 3) + 1))
            for v in variables:
                remaining[v] -= 1
            literals = [(v, rng.randrange(2)) for v in variables]
            rows.append((rng.choice(("odd", "even", "one", "atmost")), literals))
        best = len(rows)
        for x in range(1 << n):
            misses = 0
            for kind, literals in rows:
                count = sum(((x >> v) & 1) ^ s for v, s in literals)
                valid = {"odd": count % 2 == 1, "even": count % 2 == 0,
                         "one": count == 1, "atmost": count <= 1}
                misses += not valid[kind]
            best = min(best, misses)
        deficit = matching_defects(rows)
        assert deficit >= 2 * best
        assert (deficit == 0) == (best == 0)
        positive += best > 0
    return positive


def check_three_answer_exchange():
    tested = 0
    for q in range(1, 6):
        for size in (1, 2, 3):
            for relation in combinations(range(1 << q), size):
                small_diameter = all((a ^ b).bit_count() <= 2
                                     for a, b in combinations(relation, 2))
                exchange = all(
                    any((a ^ ((1 << i) | (1 << j))) in relation
                        for j in range(q) if ((a ^ b) >> j) & 1)
                    for a, b in product(relation, repeat=2)
                    for i in range(q) if ((a ^ b) >> i) & 1)
                assert small_diameter == exchange
                if size == 3 and exchange:
                    a, b, c = relation
                    majority = (a & b) | (a & c) | (b & c)
                    assert all((x ^ majority).bit_count() <= 1 for x in relation)
                tested += 1
    return tested


if __name__ == "__main__":
    total, incompatible = run_components()
    print(f"{total} connected parity/clause systems, {incompatible} incompatible")
    print("2048 labelled six-leaf trees and all 2^18 mark patterns checked")
    print(f"three-bin minimum violated split tests: {check_split_instance()}/21")
    print(f"240 matching reductions checked, {test_matching_reduction()} with a positive gap")
    print(f"{check_three_answer_exchange()} local relations of up to three answers checked")
