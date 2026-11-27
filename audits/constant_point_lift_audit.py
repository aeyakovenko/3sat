"""A nested family of simple permutations with the same three-color verdict."""

from itertools import pairwise, permutations, product

from simple_permutation_successor import red_coloring_masks, simple, valid_order


def lift(order, padding):
    """Insert padding+3 points. Removing the final new chain member recovers the previous rung."""
    if not valid_order(order) or len(order) < 4 or padding < 1:
        raise ValueError(
            "expected a permutation of length at least four and positive padding"
        )
    v = len(order) - 1
    slot = order.index(v)
    if slot == 0 or slot == v:
        raise ValueError(
            "the last identity vertex must be interior in the supplied path"
        )
    a = v + 1
    chain = tuple(range(v + 2, v + 2 + padding))
    c = v + 2 + padding
    d = c + 1
    return (
        chain[::2]
        + tuple(order[:slot])
        + (c, a, d)
        + tuple(order[slot:])
        + chain[1::2][::-1]
    )


def strip_lifts(order):
    """Recognize and remove every successive lift in linear work, even for small jumps."""
    if not valid_order(order):
        raise ValueError("expected a permutation")
    if not order:
        return (), []
    prev = [-1] * len(order)
    nxt = [-1] * len(order)
    for a, b in pairwise(order):
        prev[b], nxt[a] = a, b
    head, tail = order[0], order[-1]
    size = len(order)
    removed = []
    while size >= 8:
        d = size - 1
        v = nxt[d]
        k = d - v - 3
        if v < 3 or k < 1 or prev[d] != v + 1 or prev[v + 1] != d - 1:
            break
        first = head
        for i in range(1, k + 1, 2):
            if first != v + 1 + i:
                break
            first = nxt[first]
        else:
            last = tail
            for i in range(2, k + 1, 2):
                if last != v + 1 + i:
                    break
                last = prev[last]
            else:
                # If the left scan hits c, or the right scan hits v, v would
                # be an endpoint after deleting the proposed new vertices.
                if first == d - 1 or last == v:
                    break
                for deleted in range(v + 1, d + 1):
                    left, right = prev[deleted], nxt[deleted]
                    if left == -1:
                        head = right
                    else:
                        nxt[left] = right
                    if right == -1:
                        tail = left
                    else:
                        prev[right] = left
                size = v + 1
                removed.append(k)
                continue
        break
    base = []
    cursor = head
    while cursor != -1:
        base.append(cursor)
        cursor = nxt[cursor]
    return tuple(base), removed


def remove_point(order, removed):
    return tuple(v - int(v > removed) for v in order if v != removed)


def colorable(order):
    candidates, masks = red_coloring_masks(len(order))
    for edge in pairwise(order):
        candidates &= masks[edge]
    return bool(candidates)


def check_local_projection(k):
    # Local red positions are v=0, a=1, B_1,...,B_k, c, d.
    chain = tuple(range(2, k + 2))
    c, d = k + 2, k + 3
    left, right = chain[::2], chain[1::2][::-1]
    local_blue = [left, (c, 1, d, 0), right]
    earlier = [[] for _ in range(d + 1)]
    for path in local_blue:
        for a, b in pairwise(path):
            earlier[max(a, b)].append(min(a, b))
    rows = [(0,)]
    for j in range(1, d + 1):
        rows = [
            row + (a,)
            for row in rows
            for a in range(3)
            if row[-1] != a and all(row[i] != a for i in earlier[j])
        ]
    assert rows
    # Old v fixed to color 0. External choices are its old blue predecessor
    # and the old first/last blue vertices. They need not be distinct.
    for neighbor, first, last in product(range(3), repeat=3):
        feasible = any(
            row[c] != neighbor
            and row[left[-1]] != first
            and (not right or row[right[0]] != last)
            for row in rows
        )
        assert feasible == (neighbor != 0)


def audit():
    for k in range(1, 25):
        check_local_projection(k)
    print(
        "Endpoint projections agree for all 27 normalized cases at paddings 1 through 24."
    )
    counts = []
    for n in range(4, 9):
        count = 0
        for seed in permutations(range(n)):
            if not simple(seed):
                continue
            count += 1
            # Test the actual interval definition independent of the geometry proof.
            for k in (1, 2, 3, 4):
                new = lift(seed, k)
                assert valid_order(new) and simple(new)
                assert remove_point(lift(seed, k + 1), n + 1 + k) == new
                base, parts = strip_lifts(new)
                assert parts[0] == k
                for p in reversed(parts):
                    base = lift(base, p)
                assert base == new
        counts.append(count)
    assert counts == [2, 6, 46, 338, 2926]
    print(
        "Simplicity, literal deletion and decoding pass on all 3,318 simple seeds at sizes 4–8."
    )

    first = (5, 1, 4, 6, 3, 0, 2)
    initial = (1, 3, 0, 2)
    second = lift(initial, 1)
    assert simple(first) and not colorable(first)
    assert simple(second) and not colorable(second) and remove_point(second, 6) == first
    print("The 7-point uncolorable order 6257413 starts the infinite one-point chain.")
    large = initial
    for _ in range(100):
        large = lift(large, 1)
    assert strip_lifts(large) == (initial, [1] * 100)


if __name__ == "__main__":
    audit()
