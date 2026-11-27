"""Exact finite audits for binary projections, binary transcript choices and implication balls."""

from collections import deque
from itertools import combinations, combinations_with_replacement, product
from random import Random


def binary_hull(arity, relation):
    """Bit i of the mask represents full answer i; include empty and unary projections."""
    if not relation:
        return 0
    universe = (1 << (1 << arity)) - 1
    answer = universe
    for width in (1, 2):
        for coords in combinations(range(arity), width):
            classes = [0] * (1 << width)
            for row in range(1 << arity):
                index = sum(((row >> x) & 1) << j for j, x in enumerate(coords))
                classes[index] |= 1 << row
            for part in classes:
                if not part & relation:
                    answer &= ~part
    return answer


def check_hulls():
    relations = closed = partial_pairs = 0
    for arity in range(5):
        rows = range(1 << arity)
        universe = (1 << len(rows)) - 1
        # In fixed arity hull(R) is constant on a test of each projection class.
        forbidden_classes = []
        for width in (1, 2):
            for coords in combinations(range(arity), width):
                for bits in product((0, 1), repeat=width):
                    forbidden_classes.append(sum(1 << x for x in rows if all(
                        ((x >> c) & 1) == b for c, b in zip(coords, bits))))
        majority_rules = []
        for a, b, c in combinations(rows, 3):
            majority = (a & b) | (a & c) | (b & c)
            if majority not in (a, b, c):
                majority_rules.append(((1 << a) | (1 << b) | (1 << c), 1 << majority))
        hulls = []
        for relation in range(universe + 1):
            hull = universe if relation else 0
            for part in forbidden_classes:
                if relation & part == 0:
                    hull &= ~part
            hulls.append(hull)
            assert hull & relation == relation
            is_closed = all(relation & triple != triple or relation & median
                            for triple, median in majority_rules)
            assert is_closed == (hull == relation)
            closed += is_closed
            relations += 1
        assert all(hulls[hull] == hull for hull in hulls)
        cubes = [sum(1 << row for row in rows if all(
            b is None or (row >> j) & 1 == b for j, b in enumerate(cube)))
                 for cube in product((None, 0, 1), repeat=arity)]
        for left, right in combinations_with_replacement(cubes, 2):
            union = left | right
            assert hulls[union] == union == binary_hull(arity, union)
            partial_pairs += 1
    return relations, closed, partial_pairs


def check_transcripts():
    # Every nonempty subset of at most two transcript options over two shared bits.
    # Include the impossible test explicitly. Different transcripts can mention different bits.
    cubes = []
    for row in product((None, 0, 1), repeat=2):
        cubes.append(sum(1 << proof for proof in range(4) if all(
            b is None or (proof >> j) & 1 == b for j, b in enumerate(row))))
    tests = [()] + [(cube,) for cube in cubes] + list(combinations(cubes, 2))
    cases = 0
    for triple in combinations_with_replacement(tests, 3):
        for choices in product(*triple):
            compatible = all(a & b for a, b in combinations(choices, 2))
            assert compatible == bool(choices[0] & choices[1] & choices[2])
        accepted = [sum(1 << p for p in range(4) if any(
            opt & (1 << p) for opt in options)) for options in triple]
        for keep in subsets(range(3)):
            has_proof = any(all(accepted[i] & (1 << p) for i in keep) for p in range(4))
            has_choice = any(all(a & b for a, b in combinations(opts, 2))
                             for opts in product(*(triple[i] for i in keep)))
            assert has_proof == has_choice
        cases += 1
    return cases


def subsets(items):
    items = tuple(items)
    return (s for k in range(len(items) + 1) for s in combinations(items, k))


def bfs(start, active, edges, limit):
    parent = {start: None}
    depths = {start: 0}
    queue = deque([start])
    while queue:
        u = queue.popleft()
        if depths[u] < limit:
            for v in sorted(edges[u]):
                if v // 2 in active and v not in parent:
                    parent[v] = u
                    depths[v] = depths[u] + 1
                    queue.append(v)
    return parent, depths


def path_to(parent, v):
    path = []
    while v is not None:
        path.append(v)
        v = parent[v]
    return path[::-1]


def peel(n, forbidden, gamma_num, gamma_den):
    """Return either four certified short paths or a partial assignment and deleted variables."""
    edges = [set() for _ in range(2*n)]
    for u, v in forbidden:  # the two endpoint literals cannot both be true
        edges[u].add(v ^ 1)
        edges[v].add(u ^ 1)
    radius = 1
    while (gamma_den + gamma_num)**radius <= 2*n*gamma_den**radius:
        radius += 1
    active = set(range(n))
    deleted = set()
    assigned = {}
    while active:
        root = min(active)
        paths = []
        for source in (2*root, 2*root + 1):
            parent, depths = bfs(source, active, edges, radius)
            conflict = next((v for v in parent if v ^ 1 in parent), None)
            if conflict is not None:
                paths.extend((path_to(parent, conflict), path_to(parent, conflict ^ 1)))
                continue
            ball = {source}
            for i in range(radius):
                outer = {v for v, d in depths.items() if d == i+1}
                if gamma_den * len(outer) <= gamma_num * len(ball):
                    break
                ball.update(outer)
            else:
                raise AssertionError("ball growth exceeded literal universe")
            boundary = {v // 2 for v in outer}
            chosen = {v // 2: v % 2 for v in ball}
            assert len(chosen) == len(ball) and chosen.keys().isdisjoint(boundary)
            assert gamma_den * len(boundary) <= gamma_num * len(chosen)
            assert all(v // 2 not in active or v in ball or v // 2 in boundary
                       for u in ball for v in edges[u])
            assigned.update(chosen)
            deleted.update(boundary)
            active.difference_update(chosen, boundary)
            break
        else:
            assert len(paths) == 4
            assert paths[0][0] ^ 1 == paths[2][0]
            for first, second in (paths[:2], paths[2:]):
                assert first[0] == second[0] and first[-1] ^ 1 == second[-1]
            assert all(len(p) - 1 <= radius and all(v in edges[u] for u, v in zip(p, p[1:]))
                       for p in paths)
            core = {u // 2 for path in paths for u in path}
            assert len(core) <= 4*radius + 1
            return core, None, None
    assert assigned.keys() | deleted == set(range(n))
    assert gamma_den * len(deleted) <= gamma_num * len(assigned)
    assert all(u // 2 in deleted or v // 2 in deleted or
               (assigned[u // 2], assigned[v // 2]) != (u % 2, v % 2)
               for u, v in forbidden)
    return None, assigned, deleted


def has_choice(vertices, forbidden):
    vertices = sorted(vertices)
    local = [(u, v) for u, v in forbidden if u//2 in vertices and v//2 in vertices]
    for bits in product((0, 1), repeat=len(vertices)):
        choices = {2*v+b for v, b in zip(vertices, bits)}
        if all(u not in choices or v not in choices for u, v in local):
            return True
    return False


def check_graphs():
    counts = [0, 0, 0]  # fitted, rejected by four paths, fitted after positive deletions
    def check(n, forbidden, num, den, brute=True):
        core, assigned, deleted = peel(n, forbidden, num, den)
        if core is not None:
            if brute:
                assert not has_choice(core, forbidden)
            counts[1] += 1
        else:
            if brute:
                assert has_choice(assigned, forbidden)
            counts[0] += 1
            counts[2] += bool(deleted)
    pairs = [(2*i+a, 2*j+b) for i, j in combinations(range(3), 2)
             for a, b in product((0, 1), repeat=2)]
    for mask in range(1 << len(pairs)):
        check(3, [pair for i, pair in enumerate(pairs) if mask & (1 << i)], 1, 2)
    # Every simple graph on two literal pairs, including repeated-endpoint unary prohibitions.
    pairs = list(combinations_with_replacement(range(4), 2))
    for mask in range(1 << len(pairs)):
        check(2, [pair for i, pair in enumerate(pairs) if mask & (1 << i)], 1, 3)
    rng = Random(20261125)
    for _ in range(256):
        n = rng.randrange(4, 10)
        forbidden = [(rng.randrange(2*n), rng.randrange(2*n)) for _ in range(rng.randrange(4*n))]
        check(n, forbidden, 1, 2)
    for n in (32, 64, 128):
        # An odd-sign cycle of equality links exercises nonempty boundary deletions.
        cycle = [(2*i+b, 2*((i+1) % n) + (b ^ (i+1 != n))) for i in range(n) for b in (0, 1)]
        _, _, deleted = peel(n, cycle, 1, 2)
        assert deleted
        check(n, cycle + cycle, 1, 2, brute=False)
    return counts


if __name__ == "__main__":
    relations, closed, pairs = check_hulls()
    print(f"{relations} Boolean relations through arity 4; {closed} majority-closed hull fixed points; "
          f"{pairs} pairs of partial/full cubes preserved by the hull")
    print(f"{check_transcripts()} three-test multisets, proof and choice optima checked on all subsets")
    fitted, rejected, cut = check_graphs()
    print(f"{fitted + rejected} signed implication systems; {rejected} contradictory path witnesses, "
          f"{fitted} consistent remainders, {cut} with nonempty deletions")
