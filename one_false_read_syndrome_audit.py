"""Compare the unit-syndrome reduction and leaf extension with direct GF(2) elimination."""

from argparse import ArgumentParser
from collections import Counter, deque
from itertools import combinations, islice, permutations, product
from random import Random


def parity(value):
    return value.bit_count() % 2


def solve(rows, target, n):
    """Enumerate all solutions from reduced row echelon form, independent of the gadgets."""
    augmented = [row | (((target >> i) & 1) << n) for i, row in enumerate(rows)]
    pivots = []
    for column in range(n):
        index = len(pivots)
        pivot = next((i for i in range(index, len(rows)) if augmented[i] >> column & 1), None)
        if pivot is None:
            continue
        augmented[index], augmented[pivot] = augmented[pivot], augmented[index]
        for i in range(len(rows)):
            if i != index and augmented[i] >> column & 1:
                augmented[i] ^= augmented[index]
        pivots.append(column)
    if any(row == 1 << n for row in augmented):
        return
    free = sorted(set(range(n)) - set(pivots))
    for pattern in range(1 << len(free)):
        word = sum(((pattern >> i) & 1) << column for i, column in enumerate(free))
        for i, column in enumerate(pivots):
            word |= parity(augmented[i] & (word | (1 << n))) << column
        yield word


def graph_system(p, s):
    q = len(p)
    rows = [1 << (3 * q)]  # distinguished leaf constrains t_0
    for i in range(1, q):
        rows.append((1 << (3*q+i-1)) | (1 << (3*q+i)))
    for i in range(q):
        rows.append((1 << i) | (1 << (q+i)))
        rows.append((1 << p[i]) ^ (1 << s[i]) ^ (1 << (2*q+i)))
        rows.append((1 << (q+i)) | (1 << (2*q+i)) | (1 << (3*q+i)))
    return rows


def marked_system(p, s, h):
    q = len(p)
    return graph_system(p, s) + [(1 << (4*q)) | (1 << (q+h)) | (1 << (4*q-1))]


def amplify(rows, q, length):
    out = list(rows)
    b, s = 4*q, 4*q+1
    last = 4*q-1
    out[-1] ^= (1 << s) | (1 << last)
    out.append((1 << s) | (1 << last))
    first = s+1
    for i in range(length):
        prev = first+i-1 if i else b
        out.append((1 << prev) | (1 << (first+i)))
    c = first+length
    out.append((1 << c) | (1 << b) | (1 << s))
    for i in range(1, length):
        out.append((1 << (c+i)) | (1 << (c+i-1)))
    return out


def native_file(graph, word, bypass=False):
    """Render ordinary proper DIMACS; the selected pin name is the only private text."""
    n = len(graph)
    names = [(10*(j+1), 10*(j+1)+1) for j in range(n)]
    anchors = tuple(range(10*n+2, 10*n+5))
    clauses = []
    used = set(anchors)
    for values in product((0, 1), repeat=3):
        if any(values):
            clauses.append(tuple(-a if v else a for a, v in zip(anchors, values)))
    for j, (left, right) in enumerate(names):
        used.update((left, right))
        clauses.extend([(left, right, anchors[0]), (-left, -right, anchors[0]),
                        (names[j][word >> j & 1], *anchors[:2])])
    for name in range(1, anchors[-1]+1):
        if name not in used:
            clauses.append((-name, *anchors[:2]))
    head = [f"c root 0 bypass {int(bypass)}"]
    for i, row in enumerate(graph):
        neighbors = [j for j in range(n) if row >> j & 1]
        head.append("c row " + " ".join(map(str, neighbors)))
        if not bypass:
            for values in product((0, 1), repeat=len(neighbors)):
                if sum(values) % 2 != int(i == 0):
                    block = tuple(-names[j][1] if v else names[j][1]
                                  for j, v in zip(neighbors, values))
                    clauses.append(block + anchors[:3-len(block)])
    head.append(f"p cnf {anchors[-1]} {len(clauses)}")
    return ("\n".join(head + [" ".join(map(str, row)) + " 0" for row in clauses]) + "\n").encode()


def pinned_evaluation(raw, n, word):
    """All names have forced values; verify every ternary clause in the emitted bytes."""
    positives = {10*(j+1) + ((word >> j) & 1) for j in range(n)}
    valid = True
    lines = [line.split() for line in raw.splitlines() if not line.startswith(b"c")]
    _, _, maximum, count = lines[0]
    assert len(lines)-1 == int(count)
    for line in lines[1:]:
        a, b, c, end = map(int, line)
        assert end == 0 and len({abs(a), abs(b), abs(c)}) == 3
        assert all(0 < abs(lit) <= int(maximum) for lit in (a,b,c))
        valid &= any((abs(lit) in positives) == (lit > 0) for lit in (a,b,c))
    return valid


def audit_native(graph, words, check_models):
    for bypass in (False, True):
        base = native_file(graph, 0, bypass)
        for word in words:
            raw = native_file(graph, word, bypass)
            assert len(base) == len(raw)
            assert sum((a^b).bit_count() for a,b in zip(base, raw)) == word.bit_count()
            verdict = bypass or open_neighborhood(graph, word) == 1
            assert pinned_evaluation(raw, len(graph), word) == verdict
            if check_models:
                import pycosat

                clauses = [list(map(int, row.split()[:-1])) for row in raw.splitlines()
                           if not row.startswith((b"c", b"p"))]
                assert len(list(islice(pycosat.itersolve(clauses), 2))) == int(verdict)


def audit_patch_marker(check_models):
    from signed_permutation_cover_audit import patch

    p, s, labels, exact_covers = patch()
    q = 12
    h = 6 + labels["H0"]
    output = []
    for external in ("D", "Z0", "Z1"):
        port = labels[external]
        high = next(x for x in exact_covers if x[port])
        other = [0] * 6
        for name in ("D", "H0", "H1", "H2"):
            other[labels[name]] = 1
        witness = sum(value << i for i, value in enumerate([*high, *other]))
        p2 = list(p) + [v+6 for v in p]
        s2 = list(s) + [v+6 for v in s]
        a, b = p2.index(port), p2.index(h)
        p2[a], p2[b] = p2[b], p2[a]
        rows = marked_system(p2, s2, h)
        graph = graph_from_rows(rows, 4*q+1)
        assert max(row.bit_count() for row in graph) <= 3 and graph[0].bit_count() == 1
        mask = (1 << q) - 1
        given = witness | (witness << q) | ((mask ^ witness) << (2*q)) | (mask << (3*q))
        radius = 2*q + q//3 + 1
        assert given.bit_count() == radius + 1 and open_neighborhood(graph, given << len(rows)) == 1
        truth = any(x[port] == 0 for x in exact_covers)
        best = min(solve(graph, 1, len(graph)), key=int.bit_count)
        minimum = best.bit_count()
        audit_native(graph, [0, given << len(rows), best, 1, 2], check_models)
        assert minimum == radius + int(not truth)
        for length in (1, q):
            longer = amplify(rows, q, length)
            width = 4*q+2+2*length
            grown = graph_from_rows(longer, width)
            assert max(row.bit_count() for row in grown) <= 3
            solutions = list(solve(longer, 1, width))
            old_known = given
            new_known = next(x for x in solutions if x % (1 << (4*q+1)) == old_known)
            assert new_known.bit_count() == radius+1 + length+1
            assert min(x.bit_count() for x in solutions) == minimum + length+1
            for x in solutions:
                if x.bit_count() < new_known.bit_count():
                    assert (x ^ new_known).bit_count() >= 2*length+1
        output.append((external, truth, minimum, given.bit_count()))
    return output


def graph_from_rows(rows, n):
    graph = [row << len(rows) for row in rows] + [0] * n
    for i, row in enumerate(rows):
        while row:
            bit = row & -row
            graph[len(rows) + bit.bit_length() - 1] |= 1 << i
            row ^= bit
    return graph


def open_neighborhood(graph, word):
    return sum(parity(row & word) << i for i, row in enumerate(graph))


def extend_leaf(graph, root):
    n = len(graph)
    out = list(graph) + [(1 << root) | (1 << (n+1)), 1 << n]
    out[root] |= 1 << n
    return out


def two_contact_distance(rows, n, root):
    ground = len(rows)
    adj = [[] for _ in range(ground + 1)]
    for column in range(n):
        ends = [i for i, row in enumerate(rows) if row >> column & 1]
        assert len(ends) <= 2
        if not ends:
            continue
        if len(ends) == 1:
            ends.append(ground)
        a, b = ends
        adj[a].append(b)
        adj[b].append(a)
    distances = {root: 0}
    queue = deque([root])
    while queue:
        a = queue.popleft()
        if a == ground:
            return distances[a]
        for b in adj[a]:
            if b not in distances:
                distances[b] = distances[a] + 1
                queue.append(b)
    return None


def audit_switches(p, s):
    q = len(p)
    right = graph_system(p, s)
    graph = graph_from_rows(right, 4*q)
    assert len(graph) == 8*q and max(row.bit_count() for row in graph) <= 3
    assert graph[0].bit_count() == 1
    source = [(1 << i) ^ (1 << p[i]) ^ (1 << s[i]) for i in range(q)]
    words = list(solve(source, (1 << q) - 1, q))
    mask = (1 << q) - 1
    lifts = {x | (x << q) | ((mask ^ x) << (2*q)) | (mask << (3*q)) for x in words}
    assert set(solve(right, 1, 4*q)) == lifts
    for z in lifts:
        assert z.bit_count() == 2*q + (z & mask).bit_count()
        assert open_neighborhood(graph, z << (4*q)) == 1
    exact = any(all(((x >> i)&1) + ((x >> p[i])&1) + ((x >> s[i])&1) == 1
                    for i in range(q)) for x in words)
    # Recover a signed witness by changing one selected coefficient from +1 to -1.
    signed = any(
        all(sum(((x >> j)&1) - 2*(j == d) for j in (i, p[i], s[i])) == 1 for i in range(q))
        for x in words if x.bit_count() == q//3 + 2 for d in range(q) if x >> d & 1
    )
    if signed:
        assert min(z.bit_count() for z in lifts) == 2*q + q//3 + (0 if exact else 2)
    return signed, exact


def audit_minimal_examples():
    seeds = [
        (7, [(0,1),(1,3),(1,4),(2,6),(3,6),(4,5)], 5, [(0,4),(2,3,4)]),
        (7, [(0,4),(1,2),(1,3),(1,4),(2,5),(2,6)], 3, [(0,1,5),(0,1,6)]),
        (5, [(0,1),(1,3),(1,4),(2,3),(2,4),(3,4)], 0, [(1,2),(1,3,4)]),
    ]
    for n, edges, root, sets in seeds:
        graph = [0]*n
        for a,b in edges:
            graph[a] |= 1 << b
            graph[b] |= 1 << a
        words = {sum(1 << i for i in group) for group in sets}
        for _ in range(6):
            assert set(solve(graph, 1 << root, len(graph))) == words
            words = {word | (1 << len(graph)) for word in words}
            graph = extend_leaf(graph, root)
            root = len(graph)-1


def audit_small_graphs():
    count = count_two = realized = 0
    for n in range(1, 6):
        edges = list(combinations(range(n), 2))
        for pattern in range(1 << len(edges)):
            graph = [0] * n
            for i, (a, b) in enumerate(edges):
                if pattern >> i & 1:
                    graph[a] |= 1 << b
                    graph[b] |= 1 << a
            syndromes = [open_neighborhood(graph, word) for word in range(1 << n)]
            for root in range(n):
                old = {x for x, syndrome in enumerate(syndromes) if syndrome == 1 << root}
                new = extend_leaf(graph, root)
                enlarged = {x for x in range(1 << (n+2))
                            if open_neighborhood(new, x) == 1 << (n+1)}
                assert enlarged == {x | (1 << n) for x in old}
                realized += bool(old)
                count += 1
                if max(row.bit_count() for row in graph) <= 2:
                    assert two_contact_distance(graph, n, root) == min(
                        (x.bit_count() for x in old), default=None)
                    count_two += 1
    return count, count_two, realized


def main():
    parser = ArgumentParser()
    parser.add_argument("--picosat", action="store_true", help="check DIMACS model counts with pycosat")
    options = parser.parse_args()
    rng = Random(20261126)
    totals = Counter()
    for q in (3, 6, 9, 12):
        base = list(range(q))
        if q == 3:
            pairs = [(p, s) for p in permutations(base) for s in permutations(base)]
        else:
            pairs = [(rng.sample(base, q), rng.sample(base, q)) for _ in range(16000)]
        checked = 0
        for p, s in pairs:
            if any(len({i, p[i], s[i]}) != 3 for i in base):
                continue
            signed, exact = audit_switches(p, s)
            totals[signed, exact] += 1
            checked += 1
            if checked >= 220:
                break
    assert totals[True, True] and totals[True, False]
    print("cubic covers by (signed witness, exact cover):", sorted(totals.items()))
    print("two-patch marked graphs (port, SAT, optimum, supplied):", audit_patch_marker(options.picosat))
    audit_minimal_examples()
    count, two, realized = audit_small_graphs()
    print(f"{count} rooted graphs through 5 vertices, {realized} realizable;"
          f" {two} degree-at-most-two shortest-path comparisons")


if __name__ == "__main__":
    main()
