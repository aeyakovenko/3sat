"""Exhaust finite single-cycle observations, a scalar stopping rule, and a Horn lift."""

from collections import Counter, defaultdict
from functools import cache
from itertools import permutations
from math import comb, factorial, prod


# A group element is the bit string xyz. Left multiplication contributes x*v to z.
A, B, Z = 4, 2, 1


def multiply(left, right):
    cross = ((left >> 2) & (right >> 1)) & 1
    return left ^ right ^ cross


def cycle_table(order):
    successor = [0] * len(order)
    for u, v in zip(order, order[1:] + order[:1]):
        successor[u] = v
    return tuple(successor)


def central_bit(order):
    state = 0
    half = len(order) // 2
    for vertex in order:
        state = multiply(state, A if vertex < half else B)
    assert state in (0, Z)
    return state


def horn_satisfiable(successor):
    """Solve all ground equalities U(i,g) = U(p(i),g*h_i) with opposite pins."""
    n = len(successor)
    graph = [[] for _ in range(8 * n)]
    for i, target in enumerate(successor):
        h = A if i < n // 2 else B
        for g in range(8):
            left = 8 * i + g
            right = 8 * target + multiply(g, h)
            graph[left].append(right)
            graph[right].append(left)
    reached = {0}
    todo = [0]
    while todo:
        for node in graph[todo.pop()]:
            if node not in reached:
                reached.add(node)
                todo.append(node)
    return Z not in reached


def path_charges(n, known):
    """Recover path fragments using observed edges alone, including isolated vertices."""
    targets = set(known.values())
    charges = []
    for head in range(n):
        if head in targets:
            continue
        v = head
        charge = 0
        while True:
            charge ^= 2 if v < n // 2 else 1
            if v not in known:
                break
            v = known[v]
        charges.append(charge)
    # With every edge known the single closed component has total charge zero.
    return charges or [0]


def check_posterior(charges, signs):
    counts = [charges.count(t) for t in (1, 2, 3)]
    assert len({count % 2 for count in counts}) == 1
    difference = abs(signs[0] - signs[1])
    if counts[0] % 2:
        assert difference == 0
        return
    size = sum(counts)
    words = factorial(size) // prod(factorial(count) for count in counts)
    paired = factorial(size // 2) // prod(factorial(count // 2) for count in counts)
    assert difference * words == sum(signs.values()) * paired


def minimum_certificate(order):
    n = len(order)
    labels = [2 if v < n // 2 else 1 for v in order]
    smallest_pairing = n
    for projection in (1, 2, 3):
        marks = [i for i, label in enumerate(labels) if (label & projection).bit_count() % 2]
        assert len(marks) % 2 == 0
        if not marks:
            return 0
        gaps = [(j - i) % n for i, j in zip(marks, marks[1:] + marks[:1])]
        smallest_pairing = min(smallest_pairing, sum(gaps[::2]), sum(gaps[1::2]))
    return smallest_pairing


def certificate_sizes(orders, tables):
    # A public label renaming preserving colors identifies any two anchored color words.
    n = len(orders[0])
    representatives = {}
    for order, table in zip(orders, tables):
        colors = tuple(v < n // 2 for v in order)
        representatives.setdefault(colors, (order, table))
    for order, table in representatives.values():
        best = n
        for mask in range(1 << n):
            if mask.bit_count() >= best:
                continue
            known = {i: table[i] for i in range(n) if mask >> i & 1}
            if len(set(path_charges(n, known)) - {0}) <= 1:
                best = mask.bit_count()
        assert best == minimum_certificate(order)
    return len(representatives)


def observation_fibers(n):
    orders = [(0,) + tail for tail in permutations(range(1, n))]
    tables = list(map(cycle_table, orders))
    signs = list(map(central_bit, orders))
    assert len(set(tables)) == factorial(n - 1)
    frequencies = Counter(signs)
    assert frequencies[0] > frequencies[1] > 0
    # Pair adjacent positions of a color word. On words with a mixed pair,
    # flipping the first mixed pair reverses sign. Monochromatic pairs give sign zero.
    expected_bias_numerator = comb(n // 2, n // 4)
    assert (frequencies[0] - frequencies[1]) * comb(n, n // 2) == len(orders) * expected_bias_numerator
    for table, sign in zip(tables, signs):
        assert horn_satisfiable(table) == (sign == 0)

    fibers = 0
    half = n // 2
    # Color-preserving relabeling acts transitively on query sets with these two sizes.
    # Anchoring 0 just indexes cycles: every cycle product is central and rotation-invariant.
    for reds in range(half + 1):
        for blues in range(half + 1):
            queried = tuple(range(reds)) + tuple(range(half, half + blues))
            completions = defaultdict(Counter)
            for table, sign in zip(tables, signs):
                completions[tuple(table[i] for i in queried)][sign] += 1
            fragments = n - len(queried)
            for replies, possible in completions.items():
                charges = path_charges(n, dict(zip(queried, replies)))
                decisive = len(set(charges) - {0}) <= 1
                assert (len(possible) == 1) == decisive
                assert sum(possible.values()) == factorial(max(0, fragments - 1))
                check_posterior(charges, possible)
                fibers += 1
    return fibers, frequencies, certificate_sizes(orders, tables)


def exact_scalar_stopping(n, active):
    """Optimize choice of every labeled tail, retaining the fragment vertex sets."""
    @cache
    def solve(fragments):
        c = len(fragments)
        odd = sum((s & active).bit_count() % 2 for s in fragments)
        assert odd % 2 == 0
        if odd == 0:
            numerator = c * factorial(c - 1)
        else:
            # Each head of a different fragment has (c-2)! labeled cyclic completions.
            # Internal orientations no longer affect this scalar stopping condition.
            options = []
            for i, first in enumerate(fragments):
                value = 0
                for j, second in enumerate(fragments):
                    if i == j:
                        continue
                    rest = [s for s in fragments if s != first and s != second]
                    child = tuple(sorted(rest + [first | second]))
                    value += solve(child)
                options.append(value)
            numerator = max(options)

        # numerator/(c-1)! is the actual optimal expected remaining count.
        left, right = numerator, c * factorial(c - 1)
        for j in range(2, odd + 1, 2):
            left *= j
            right *= j - 1
        assert left == right
        return numerator

    solve(tuple(1 << i for i in range(n)))
    return solve.cache_info().currsize


def main():
    for n in (4, 8):
        fibers, signs, certificate_tests = observation_fibers(n)
        red = (1 << (n // 2)) - 1
        blue = red << (n // 2)
        states = sum(exact_scalar_stopping(n, active) for active in (red, blue, red | blue))
        print(f"n={n}: {fibers:,} partial-map fibers up to query-set symmetry; "
              f"{certificate_tests} anchored color words with exact certificate costs; "
              f"{states:,} scalar stopping states; {signs[0]:,} SAT and {signs[1]:,} UNSAT cycle lifts.")


if __name__ == "__main__":
    main()
