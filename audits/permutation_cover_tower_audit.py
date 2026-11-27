"""Check the small levels of the two-permutation congruence tower."""

from collections import deque
from itertools import combinations, permutations


def matrix_group(k):
    modulus = 1 << k
    group = [(1, 0, 0, 1)]
    index = {group[0]: 0}
    right_a, right_b = [], []
    for a, b, c, d in group:
        images = ((a, 2*a+b, c, 2*c+d), (a+2*b, b, c+2*d, d))
        for matrix, action in zip(images, (right_a, right_b)):
            reduced = tuple(x % modulus for x in matrix)
            if reduced not in index:
                index[reduced] = len(group)
                group.append(reduced)
            action.append(index[reduced])
    return group, right_a, right_b


def lift(action, shift):
    d = len(action)
    return [((s + shift) % 3) * d + image for s in range(3) for image in action]


def residue_test(p, q, a, b):
    """Propagate along forward arcs, sufficient because the arrays are permutations."""
    n = len(p)
    z = [None] * n
    component_sizes = []
    for start in range(n):
        if z[start] is not None:
            continue
        z[start] = 0
        queue = deque([start])
        size = 0
        while queue:
            u = queue.popleft()
            size += 1
            for v, delta in ((p[u], a), (q[u], b)):
                value = (z[u] + delta) % 3
                if z[v] is None:
                    z[v] = value
                    queue.append(v)
                elif value != z[v]:
                    return None
        component_sizes.append(size)
    return z, component_sizes


def covers(p, q, choice):
    touched = [u for i in choice for u in (i, p[i], q[i])]
    return len(touched) == len(p) and len(set(touched)) == len(p)


def brute_count(p, q):
    if len(p) % 3:
        return 0
    return sum(covers(p, q, s) for s in combinations(range(len(p)), len(p)//3))


def girth(p, q):
    # Left multiplication in the voltage group is transitive on each side.
    n = len(p)
    edges = [[] for _ in range(2*n)]
    for i in range(n):
        for color, j in enumerate((i, p[i], q[i])):
            j += n
            edges[i].append((j, color))
            edges[j].append((i, color))
    best = None
    for root in (0, n):
        depth, parent_color = {root: 0}, {root: -1}
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v, color in edges[u]:
                if color == parent_color[u]:
                    continue
                if v in depth:
                    length = depth[u] + depth[v] + 1
                    best = length if best is None else min(best, length)
                else:
                    parent_color[v] = color
                    depth[v] = depth[u] + 1
                    queue.append(v)
    return best


def main():
    n = 3
    all_perm = list(permutations(range(n)))
    base_yes = sum(bool(brute_count(p, q)) for p in all_perm for q in all_perm)
    print(f"three points: {base_yes} yes, {len(all_perm)**2-base_yes} no")
    prev_group = None
    for k in range(1, 7):
        group, right_a, right_b = matrix_group(k)
        d = len(group)
        assert d & (d-1) == 0
        if prev_group is not None:
            previous = {matrix: i for i, matrix in enumerate(prev_group)}
            reduction = [previous[tuple(x % (1 << (k-1)) for x in g)] for g in group]
            for action, old_action in ((right_a, old_a), (right_b, old_b)):
                assert all(reduction[image] == old_action[reduction[u]]
                           for u, image in enumerate(action))
        girths = []
        for a, b in ((1, 2), (0, 1)):
            p, q = lift(right_a, a), lift(right_b, b)
            n = len(p)
            assert len(set(p)) == len(set(q)) == n
            labels, sizes = residue_test(p, q, a, b)
            assert sizes == [n]
            if a == 1:
                assert covers(p, q, [u for u in range(n) if labels[u] == 0])
            else:
                assert all(labels.count(i) == d for i in range(3)) and d % 3
            assert residue_test(p, q, 1-a, 3-b) is None
            if n <= 12:
                assert bool(brute_count(p, q)) == (a == 1)
            g = girth(p, q)
            assert 3**g + 1 >= 2**k
            girths.append(g)
        print(f"k={k}, q={3*d}, girths {girths[0]}/{girths[1]}")
        prev_group, old_a, old_b = group, right_a, right_b


if __name__ == "__main__":
    main()
