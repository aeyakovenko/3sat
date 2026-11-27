"""Finite coefficient and moment checks for partial Boolean multilinearization."""

from itertools import combinations, permutations, product


def subsets(items, maximum):
    for size in range(min(len(items), maximum) + 1):
        yield from combinations(items, size)


def correct_monomial(exponents, budget, prime):
    """Apply the truncated difference operators symbolically, then collect terms."""
    coefficients = {}
    for selected in subsets(range(len(exponents)), budget):
        # D_i sends x^e to x-x^e for e>=2 and annihilates smaller powers.
        if any(exponents[i] < 2 for i in selected):
            continue
        for lowered in subsets(selected, len(selected)):
            term = list(exponents)
            for i in lowered:
                term[i] = 1
            key = tuple(term)
            sign = (-1) ** (len(selected) - len(lowered))
            coefficients[key] = (coefficients.get(key, 0) + sign) % prime
    return {term: c for term, c in coefficients.items() if c}


def check_corrections():
    tested = 0
    for exponents in product(range(4), repeat=4):
        support = sum(e > 0 for e in exponents)
        repeats = sum(e > 1 for e in exponents)
        multilinear = tuple(int(e > 0) for e in exponents)
        for budget in range(5):
            actual = correct_monomial(exponents, budget, 5)
            for degree in range(5):
                if support <= degree and repeats > budget:
                    continue
                low = {term: c for term, c in actual.items() if sum(term) <= degree}
                assert low == ({multilinear: 1} if support <= degree else {})
                tested += 1
    # Smaller support can be polluted by powers even when only one degree matters.
    assert correct_monomial((2, 0), 0, 5) == {(2, 0): 1}
    return tested


def gf4_mul(a, b):
    """Multiply binary coefficient vectors modulo t^2+t+1."""
    times_t = (a << 1) ^ (7 if a & 2 else 0)
    return (a if b & 1 else 0) ^ (times_t if b & 2 else 0)


def gf4_product(values):
    result = 1
    for value in values:
        result = gf4_mul(result, value)
    return result


def check_moments(coordinates, degree):
    z = [2 + i % 2 for i in range(coordinates)]
    indices = list(subsets(range(coordinates), degree))
    rows = []
    for point in product((0, 1), repeat=coordinates):
        weight = gf4_product(z[i] if bit else 1 ^ z[i] for i, bit in enumerate(point))
        basis = [gf4_product(point[i] ^ z[i] for i in s) for s in indices]
        rows.append((weight, basis))
    for left, s in enumerate(indices):
        for right, t in enumerate(indices):
            moment = 0
            for weight, values in rows:
                moment ^= gf4_product((weight, values[left], values[right]))
            expected = gf4_product(gf4_mul(z[i], 1 ^ z[i]) for i in s) if s == t else 0
            assert moment == expected
            assert (moment != 0) == (s == t)
    return len(indices)


def check_cycle_projection(k, padding):
    """Enumerate spanning cycles and their original edge labels after degree splits."""
    arcs = {(u, v): (u, v) for u in range(k) for v in range(k) if u != v}
    size = k
    for incoming in (True, False):
        vertex = 0
        while vertex < size:
            side = [e for e in arcs if e[1 if incoming else 0] == vertex]
            if len(side) > 3:
                a, b = size, size + 1
                size += 2
                for i, (u, v) in enumerate(side):
                    target = a if i < len(side) // 2 else b
                    edge = (u, target) if incoming else (target, v)
                    arcs[edge] = arcs.pop((u, v))
                internal = [(a, b), (b, a), (a, vertex), (b, vertex)]
                for u, v in internal:
                    arcs[(u, v) if incoming else (v, u)] = None
            vertex += 1
    for _ in range(padding):
        for edge in [e for e in arcs if e[0] == 0]:
            arcs[size, edge[1]] = arcs.pop(edge)
        arcs[0, size] = None
        size += 1
    neighbors = [[v for u, v in arcs if u == i] for i in range(size)]
    assert all(len(out) <= 3 for out in neighbors)
    assert all(sum(v == i for _, v in arcs) <= 3 for i in range(size))
    projected = set()

    def visit(u, seen, labels):
        for v in neighbors[u]:
            label = arcs[u, v]
            updated = labels if label is None else labels | {label}
            if v == 0 and len(seen) == size:
                assert updated not in projected
                projected.add(updated)
            elif v not in seen:
                visit(v, seen | {v}, updated)

    visit(0, {0}, frozenset())
    expected = set()
    for tail in permutations(range(1, k)):
        cycle = (0,) + tail
        expected.add(frozenset(zip(cycle, cycle[1:] + (0,))))
    assert projected == expected
    return size, len(projected)


if __name__ == "__main__":
    print(f"GF(5) low-degree coefficient checks: {check_corrections()}")
    print(f"GF(4) nonsingular moment matrix dimension: {check_moments(6, 3)}")
    for k in (4, 5):
        size, count = check_cycle_projection(k, padding=3)
        print(f"HC_{k}: all {count} cycles lift uniquely on {size} vertices.")
