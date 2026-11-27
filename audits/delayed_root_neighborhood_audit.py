"""Check equal signed root neighborhoods on opposite degree-four NAE-root formulas."""

from collections import Counter, defaultdict, deque
from itertools import combinations, product

from almost_mixed_cutoff_audit import checked_solve, two_exception_formula
from one_byte_dense_successor_audit import parse


def sources():
    edges = {edge: i + 1 for i, edge in enumerate(combinations(range(4), 2))}
    rows = []
    for vertex in range(4):
        names = [name for edge, name in edges.items() if vertex in edge]
        for bits in product((0, 1), repeat=3):
            if sum(bits) % 2 != int(vertex == 0):
                rows.append(tuple(-x if bit else x for x, bit in zip(names, bits)))
    # The charge sum is odd. Two edits at vertex zero replace two forbidden
    # local configurations by the neighbors along the same edge coordinate.
    right = next(j for j in range(1, 4) if rows[j][0] == -rows[0][0])
    changed = list(rows)
    for j in (0, right):
        a, b, c = changed[j]
        changed[j] = (-a, b, c)
    def models(source):
        return [bits for bits in product((False, True), repeat=6)
                if all(any(bits[abs(lit) - 1] == (lit > 0) for lit in row)
                       for row in source)]
    assert not models(rows) and len(models(changed)) == 4
    assert not checked_solve(rows, []) and checked_solve(changed, [])
    return rows, changed


def clause_key(row):
    return tuple(map(abs, row)), tuple(x < 0 for x in row)


def body(raw):
    clauses = parse(raw)
    positive, = [r for r in clauses if min(r) > 0]
    negative, = [r for r in clauses if max(r) < 0]
    assert positive == tuple(-x for x in negative)
    return clauses, positive, sorted(clauses - {positive, negative}, key=clause_key)


def distances(rows, roots):
    # Positive integers are variable vertices and negative integers are clause IDs.
    graph = defaultdict(list)
    for i, row in enumerate(rows, 1):
        for literal in row:
            graph[abs(literal)].append(-i)
            graph[-i].append(abs(literal))
    result = {node: 0 for node in roots}
    queue = deque(roots)
    while queue:
        u = queue.popleft()
        for node in graph[u]:
            if node not in result:
                result[node] = result[u] + 1
                queue.append(node)
    return result


def audit(source_pair, delay, regular):
    left, right = [two_exception_formula(src, regular, prefix_delay=delay) for src in source_pair]
    assert len(left) == len(right) and Counter(left) == Counter(right)
    first, roots, xs = body(left)
    second, right_roots, ys = body(right)
    assert roots == right_roots and len(xs) == len(ys)
    assert not checked_solve(first, []) and checked_solve(second, [])
    degrees = Counter(abs(z) for row in first for z in row)
    assert max(degrees.values()) <= 4
    if regular:
        assert set(degrees.values()) == {4}
    distance = distances(xs, roots)
    changes = []
    for i, (x, y) in enumerate(zip(xs, ys), 1):
        assert tuple(map(abs, x)) == tuple(map(abs, y))
        for a, b in zip(x, y):
            if a != b:
                assert a == -b
                changes.append(min(distance[-i], distance[abs(a)]))
    assert len(changes) == 2
    # The radius declared here is conservative; both endpoints of every
    # signed incidence touching this ball are unchanged.
    assert min(changes) > delay
    return len(left), min(changes)


if __name__ == '__main__':
    tests = sources()
    for regular in (False, True):
        for delay in (0, 1, 8, 32, 64):
            size, distance = audit(tests, delay, regular)
            print(f'regular={regular}, delay {delay}, {size:,} bytes, nearest changed incidence {distance}')
        empty = two_exception_formula([], regular, prefix_delay=8)
        rows, roots, mixed = body(empty)
        assert checked_solve(rows, [])
        assert all(checked_solve(mixed, [x if bit else -x for bit, x in zip(setting, roots)])
                   for setting in product((False, True), repeat=3))
