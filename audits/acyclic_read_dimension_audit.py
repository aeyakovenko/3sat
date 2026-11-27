"""Exhaustive small-graph test of the minimum-size forest for a centered affine load."""

from itertools import combinations, product
from random import Random


def indices(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def submasks(mask):
    candidate = mask
    while True:
        yield candidate
        if candidate == 0:
            return
        candidate = (candidate - 1) & mask


def flat_restrictions(n):
    """All zero-centered flats, with the linear truth tables on each one."""
    forms = [
        sum(((x & coefficient).bit_count() % 2) << x for x in range(1 << n))
        for coefficient in range(1 << n)
    ]
    by_dimension = [[] for _ in range(n + 1)]
    for d in range(n + 1):
        for pivots in combinations(range(n), d):
            choices = []
            for lead in pivots:
                rows = [1 << lead]
                for column in range(lead + 1, n):
                    if column not in pivots:
                        rows += [r | (1 << column) for r in rows]
                choices.append(rows)
            for basis in product(*choices):
                span = [0]
                for row in basis:
                    span += [x ^ row for x in span]
                space = sum(1 << x for x in span)
                by_dimension[d].append((space, {f & space for f in forms}))
    return by_dimension


def is_forest(n, edges):
    labels = list(range(n))
    for u, v in edges:
        left, right = labels[u], labels[v]
        if left == right:
            return False
        labels = [left if x == right else x for x in labels]
    return True


def maximum_matching(edges):
    best = []
    for mask in range(1 << len(edges)):
        if mask.bit_count() <= len(best):
            continue
        chosen = [edges[i] for i in indices(mask)]
        if len({v for e in chosen for v in e}) == 2 * len(chosen):
            best = chosen
    return best


def cnf_has_model(clauses, variables):
    def satisfied(lit, assignment):
        return bool(assignment >> (abs(lit) - 1) & 1) == (lit > 0)

    return any(
        all(any(satisfied(lit, assignment) for lit in clause) for clause in clauses)
        for assignment in range(1 << variables)
    )


def cover_orientation_cnf(n, edges, matching, extra=(), require=()):
    """One endpoint per matched pair; an exception makes a single or both fixed true."""
    literal = [0] * n  # zero is false, None is true
    for j, (a, b) in enumerate(matching, start=1):
        literal[a], literal[b] = j, -j
    for v in extra:
        literal[v] = None
    clauses = []
    for row in [*edges, *((v,) for v in require)]:
        clause = [literal[v] for v in row]
        if None not in clause:
            clauses.append([lit for lit in clause if lit != 0])
    return clauses


def audit_graphs():
    total = pairs = exact_both = near = 0
    for n in range(6):
        universe = list(combinations(range(n), 2))
        flats = flat_restrictions(n)
        facts = []
        for mask in range(1 << len(universe)):
            edges = [universe[i] for i in indices(mask)]
            edge_bits = [(1 << u) | (1 << v) for u, v in edges]
            truth = sum(any(x & e == e for e in edge_bits) << x for x in range(1 << n))
            alpha = max(x.bit_count() for x in range(1 << n) if not (truth >> x & 1))
            affine = max(
                d for d, spaces in enumerate(flats)
                if any(truth & space in allowed for space, allowed in spaces)
            )
            facts.append((alpha, affine, is_forest(n, edges)))

        for mask, (alpha, affine, _) in enumerate(facts):
            edges = [universe[i] for i in indices(mask)]
            matching = maximum_matching(edges)
            nu = len(matching)
            tau = n - alpha
            gap = tau - nu
            delta = affine - alpha
            min_size = {}
            both_min = None
            for h in submasks(mask):
                alpha_h, affine_h, acyclic = facts[h]
                if not acyclic:
                    continue
                pairs += 1
                size = h.bit_count()
                min_size[affine_h] = min(size, min_size.get(affine_h, size))
                if alpha_h == alpha and affine_h == affine:
                    both_min = size if both_min is None else min(both_min, size)
            assert min_size == {t: n - t for t in range(n - nu, n + 1)}
            assert (affine in min_size) == (gap <= 1)
            assert min(abs(t - affine) for t in min_size) == max(0, gap - 1)
            assert both_min == (nu + delta if gap == 0 else None)
            exact_both += both_min is not None

            def has_cover(extra=(), require=()):
                clauses = cover_orientation_cnf(n, edges, matching, extra, require)
                return cnf_has_model(clauses, nu)

            covered = {v for e in matching for v in e}
            exceptions = [*matching, *((v,) for v in range(n) if v not in covered)]
            at_matching = has_cover()
            within_one = at_matching or any(has_cover(option) for option in exceptions)
            assert at_matching == (gap == 0)
            assert within_one == (gap <= 1)
            if at_matching:
                assert any(has_cover(require=e) for e in edges) == bool(delta)
            near += within_one
            total += 1
    return total, pairs, exact_both, near


def prefix_counterexample():
    # Two disjoint edges, then a linking edge, then the closing edge of C4.
    n = 4
    ordered = [(0, 1), (2, 3), (1, 2), (0, 3)]
    flats = flat_restrictions(n)

    def dimension(mask):
        edges = [(1 << ordered[i][0]) | (1 << ordered[i][1]) for i in indices(mask)]
        truth = sum(any(x & e == e for e in edges) << x for x in range(1 << n))
        return max(
            d for d, spaces in enumerate(flats)
            if any(truth & space in allowed for space, allowed in spaces)
        )

    full = (1 << len(ordered)) - 1
    thresholds = [(1 << i) - 1 for i in range(len(ordered) + 1)]
    targets = [dimension(t) for t in thresholds]
    assert targets == [4, 3, 2, 3, 2]
    for h in submasks(full):
        if is_forest(n, [ordered[i] for i in indices(h)]):
            assert [dimension(t & h) for t in thresholds] != targets
    return targets


def staircase_profiles(s):
    edges = [
        (i - 1, s + j - 1, i + j - 1)
        for i in range(1, s + 1)
        for j in range(1, s + 1)
        if i + j - 1 <= s
    ]
    masks = [(1 << u) | (1 << v) for u, v, _ in edges]
    all_vertices = (1 << (2 * s)) - 1
    full = (1 << len(edges)) - 1
    ranks = []
    for included in range(full + 1):
        selected = [masks[i] for i in indices(included)]
        stable = [x for x in range(all_vertices + 1) if not any(x & e == e for e in selected)]
        alpha = max(x.bit_count() for x in stable)
        extra = any(
            x.bit_count() == alpha and any((all_vertices ^ x) & e == e for e in selected)
            for x in stable
        )
        ranks.append((alpha, extra))
    levels = [
        sum(1 << i for i, (_, _, w) in enumerate(edges) if w <= t)
        for t in range(1, s + 1)
    ]
    return [
        (h.bit_count(), [ranks[h & level] for level in levels])
        for h in range(full + 1)
    ]


def staircase_bound(q, s, error):
    # A retained perfect matching in an active copy forces all t new edges.
    through_matching = max(0, q - error)
    per_full = q - error if q >= 2 * error + 2 else q - error - 1
    through_matching += max(0, per_full) * sum(range(2, s + 1))
    # In disjoint weight windows (t-width,t], count forced near-frontier edges
    # using the sum of t-weight over a maximum matching and optimize the windows.
    windows = [0]
    for t in range(1, s + 1):
        best = windows[-1]
        for width in range(1, t + 1):
            hits = q * t - error - 1 - t * (error + 1) // width
            best = max(best, windows[t - width] + max(0, hits))
        windows.append(best)
    return max(through_matching, windows[-1])


def staircase_test(q, s):
    profiles = staircase_profiles(s)
    _, full = profiles[-1]
    targets = [q * alpha + int(extra) for alpha, extra in full]
    best = [q * profiles[-1][0] + 1] * (q * s + 1)
    # Components have additive independent numbers; the extra dimension
    # occurs precisely when it occurs in at least one component.
    for copies in product(profiles, repeat=q):
        count = sum(size for size, _ in copies)
        error = 0
        for t, target in enumerate(targets):
            values = [levels[t] for _, levels in copies]
            dim = sum(a for a, _ in values) + int(any(d for _, d in values))
            error = max(error, abs(dim - target))
        best[error] = min(best[error], count)
    for b in range(1, len(best)):
        best[b] = min(best[b], best[b - 1])
    assert best[0] == q * s * (s + 1) // 2
    for b, size in enumerate(best):
        assert size >= staircase_bound(q, s, b)
    return best


def staircase_shortfalls():
    matchings = 0
    for t in range(1, 6):
        edges = [(i, j) for i in range(1, t + 1) for j in range(1, t + 2 - i)]
        for mask in range(1 << len(edges)):
            chosen = [edges[h] for h in indices(mask)]
            r = len(chosen)
            if len({i for i, _ in chosen}) != r or len({j for _, j in chosen}) != r:
                continue
            shortfall = sum(t + 1 - i - j for i, j in chosen)
            assert shortfall <= r * (t - r)
            matchings += 1
    return matchings


def bipartite_affine_dimension(s, edges):
    neighbors = [[] for _ in range(s)]
    for i, j in edges:
        neighbors[i].append(j)

    def matching_size(ignore_left=-1, ignore_right=-1):
        owner = [-1] * s

        def augment(i, seen):
            for j in neighbors[i]:
                if j == ignore_right or j in seen:
                    continue
                seen.add(j)
                if owner[j] == -1 or augment(owner[j], seen):
                    owner[j] = i
                    return True
            return False

        return sum(augment(i, set()) for i in range(s) if i != ignore_left)

    nu = matching_size()
    # A largest independent set excludes the endpoints of edge ij exactly
    # when deleting both preserves alpha, equivalently drops nu by two.
    extra = any(matching_size(i, j) == nu - 2 for i, j in edges)
    return 2 * s - nu + extra


def sampled_staircases():
    comparisons = 0
    for s in range(1, 11):
        all_edges = [(i, j) for i in range(s) for j in range(s - i)]
        for error in range(1, s + 1):
            retained = [(i, j) for i, j in all_edges if (i + j + 1) % error == 0]
            levels = s // error
            assert len(retained) == error * levels * (levels + 1) // 2
            for t in range(s + 1):
                full_now = [(i, j) for i, j in all_edges if i + j + 1 <= t]
                sparse_now = [(i, j) for i, j in retained if i + j + 1 <= t]
                observed = bipartite_affine_dimension(s, full_now)
                sparse = bipartite_affine_dimension(s, sparse_now)
                assert observed == 2 * s - t + (t >= 2)
                assert abs(observed - sparse) <= error
                comparisons += 1
    return comparisons


def components(n, arcs, weak=False):
    reach = [[i == j for j in range(n)] for i in range(n)]
    for i, j in arcs:
        reach[i][j] = True
        if weak:
            reach[j][i] = True
    for k in range(n):
        for i in range(n):
            if reach[i][k]:
                for j in range(n):
                    reach[i][j] |= reach[k][j]
    return [min(j for j in range(n) if reach[i][j] and reach[j][i]) for i in range(n)]


def copy_merge_trees(edges, chosen, old, new):
    for group in set(new):
        children = {old[i] for i in range(len(old)) if new[i] == group}
        for reverse in [False, True]:
            visited = {min(children)}
            while visited != children:
                for arc in edges:
                    x, y = arc[::-1] if reverse else arc
                    if old[x] in visited and old[y] in children - visited:
                        chosen.add(arc)
                        visited.add(old[y])
                        break
                else:
                    raise AssertionError("the contracted component has no next tree edge")


def perfect_matching_prefixes(n, weights):
    # Arc j->i represents L_i R_j; all n matched edges are present initially.
    selected = set()
    labels = list(range(n))
    for x, y in sorted(weights, key=lambda a: (weights[a], a)):
        left, right = labels[x], labels[y]
        if left != right:
            selected.add((x, y))
            labels = [left if c == right else c for c in labels]
    old = list(range(n))
    thresholds = sorted({0, *weights.values()})
    for t in thresholds:
        edges = [a for a, w in weights.items() if w <= t]
        new = components(n, edges)
        copy_merge_trees(edges, selected, old, new)
        old = new
    assert n + len(selected) <= 4 * n - 3
    for t in thresholds:
        edges = {a for a, w in weights.items() if w <= t}
        kept = edges & selected
        strong = components(n, edges)
        weak = components(n, edges, weak=True)
        assert components(n, kept) == strong
        assert components(n, kept, weak=True) == weak
        # Enumerate the maximum independent sets choosing one vertex per pair.
        def extra(arcs):
            for left in range(1 << n):
                if any(left >> i & 1 and not left >> j & 1 for j, i in arcs):
                    continue
                if any(left >> j & 1 and not left >> i & 1 for j, i in arcs):
                    return True
            return False

        assert extra(edges) == (weak != strong) == extra(kept)
    return len(thresholds)


def persistent_matchings():
    checked = 0
    arcs = [(i, j) for i in range(3) for j in range(3) if i != j]
    for levels in product((-1, 0, 1), repeat=len(arcs)):
        checked += perfect_matching_prefixes(3, {a: w for a, w in zip(arcs, levels) if w >= 0})
    rng = Random(271828)
    for n in range(4, 8):
        for _ in range(40):
            weights = {}
            for i in range(n):
                for j in range(n):
                    if i != j and rng.randrange(3):
                        weights[i, j] = rng.randrange(5)
            checked += perfect_matching_prefixes(n, weights)
    return checked


if __name__ == "__main__":
    total, pairs, both, near = audit_graphs()
    print(f"{total} graphs and {pairs} acyclic subgraphs passed the size and distance tests")
    print(f"{both} preserve both dimensions; {near} pass the near-matching 2-CNF test")
    print(f"C4 threshold dimensions {prefix_counterexample()} require all four edges")
    for copies, size in [(2, 2), (2, 3), (4, 2)]:
        print(f"Staircase q={copies}, s={size}: minimum edges by additive error {staircase_test(copies, size)}")
    print(f"{staircase_shortfalls()} staircase matchings passed the weighted shortfall inequality")
    print(f"{sampled_staircases()} sampled staircase prefixes attained their advertised additive error")
    print(f"{persistent_matchings()} perfect-matching prefixes preserved both partitions and affine dimension")
