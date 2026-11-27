"""Check projected hulls, sparse hole counts and positive-query ambiguity."""

from itertools import combinations, permutations, product


def build_hull(v, width, witness):
    cube = tuple(range(1 << v))
    hull = set(cube)
    for arity in range(width + 1):
        for coordinates in combinations(range(v), arity):
            mask = sum(1 << coordinate for coordinate in coordinates)
            possible = {x & mask for x in witness}
            hull.intersection_update(x for x in cube if x & mask in possible)
    return hull


def check_hulls():
    count = 0
    for v in range(1, 4):
        cube = tuple(range(1 << v))
        for bits in range(1 << len(cube)):
            witness = {x for x in cube if bits >> x & 1}
            for d in range(1, v + 1):
                hull = build_hull(v, d, witness)
                assert witness <= hull
                holes = tuple(sorted(hull - witness))
                for r in range(len(cube) + 2):
                    valid = any(all(x not in witness for x in group)
                                for group in combinations(hull, r))
                    assert valid == (len(holes) >= r)
                assert (len(hull) - len(holes)) % 2 == len(witness) % 2
                count += 1
    return count


def check_tables():
    count = 0
    for v in range(1, 5):
        cube = tuple(range(1 << v))
        # Include every monomial that misses some variable. Linearity then
        # gives zero parity for their XOR without enumerating all polynomials.
        for monomial in range((1 << v) - 1):
            values = [(x & monomial) == monomial for x in cube]
            assert sum(values) % 2 == 0
            count += 1
    return count


def check_one_point_repairs():
    checks = 0
    for v in range(1, 4):
        size = 1 << v
        for truth in range(1 << size):
            if truth.bit_count() % 2 == 0:
                continue
            for point in range(size):
                repair = truth ^ (1 << point)
                coefficients = [(repair >> x) & 1 for x in range(size)]
                for i in range(v):
                    for mask in range(size):
                        if mask & (1 << i):
                            coefficients[mask] ^= coefficients[mask ^ (1 << i)]
                assert coefficients[-1] == 0
                for x in range(size):
                    value = sum(coefficients[m] for m in range(size) if m & x == m) % 2
                    assert value == (repair >> x) & 1
                checks += 1
    return checks


def check_two_holes():
    pairs = 0
    for v in range(2, 6):
        cube = set(range(1 << v))
        for s, u in combinations(cube, 2):
            if (s ^ u).bit_count() < 2:
                continue
            for remaining in (cube - {s}, cube - {s, u}):
                assert build_hull(v, v - 1, remaining) == cube
            pairs += 1
    # Simulate every subset query on a tiny example. Protect just one witness
    # per positive response. Each unprotected one-point alteration is invisible.
    cube = set(range(8))
    base = cube - {0}
    for mask in range(1 << len(cube)):
        query = {x for x in cube if mask >> x & 1}
        hits = query & base
        saved = min(hits) if hits else None
        for u in (3, 5, 6, 7):
            if u != saved:
                assert bool(query & (base - {u})) == bool(hits)
    return pairs


def majority_rows(left, right, third, out):
    return (all(not (a and b) or out for a, b in combinations((left, right, third), 2))
            and all(a or b or not out for a, b in combinations((left, right, third), 2)))


def check_closed_circuits():
    assignments = 0
    for first, second, op1, op2, neg in product(range(2), repeat=5):
        # Inputs are constant gates. The last gate may negate its predecessor.
        v1 = (first or second) if op1 else (first and second)
        v2 = (v1 or first) if op2 else (v1 and first)
        output = v2 ^ neg
        actual = (first, second, v1, v2, output)
        for color in range(2):
            solutions = []
            for tag, *raw in product(range(2), repeat=6):
                valid = (raw[0] == first ^ tag and raw[1] == second ^ tag
                         and majority_rows(raw[0], raw[1], tag ^ op1, raw[2])
                         and majority_rows(raw[2], raw[0], tag ^ op2, raw[3])
                         and raw[4] == raw[3] ^ neg)
                if valid and (not tag or raw[4] == color):
                    solutions.append((tag, *raw))
                assignments += 1
            expected = [(0, *actual)]
            if output != color:
                expected.append((1, *(x ^ 1 for x in actual)))
            assert solutions == expected
    return assignments


def check_native_logs():
    checked = 0
    for put_at, first_word, get_at in product(range(2), repeat=3):
        passing = []
        for bits in product(range(2), repeat=12):
            rows = [bits[t:t + 3] for t in range(0, len(bits), 3)]
            # (address, old, new). The third access is disabled after reading 0.
            (a, b, c, d) = rows
            enabled = (True, True, bool(b[1]), True)
            cpu = (a[0] == put_at and a[2] == first_word
                   and b[0] == get_at and b[1] == b[2]
                   and ((c[0] == b[1] and c[2] == 0) if enabled[2] else c == (0, 0, 0))
                   and d[0] == 1 and d[2] == d[1])
            if not cpu:
                continue
            keys = [(not enabled[i], row[0], i) for i, row in enumerate(rows)]
            order = sorted(range(4), key=keys.__getitem__)
            last_address = None
            last_value = None
            memory_valid = True
            for i in order:
                if not enabled[i]:
                    continue
                address, old, new = rows[i]
                memory_valid &= old == (last_value if address == last_address else 0)
                last_address, last_value = address, new
            if memory_valid:
                passing.append((rows, keys))
            checked += 1
        assert len(passing) == 1
        rows, keys = passing[0]
        scratch = [0, 0]
        scratch[put_at] = first_word
        if scratch[get_at]:
            scratch[1] = 0
        assert rows[-1][-1] == scratch[1]
        orders = [perm for perm in permutations(range(4))
                  if all(keys[a] < keys[b] for a, b in zip(perm, perm[1:]))]
        assert len(orders) == 1
        (order,) = orders
        assert sum(all(inv[order[pos]] == pos for pos in range(4))
                   for inv in permutations(range(4))) == 1
    return checked


if __name__ == "__main__":
    print(f"Checked {check_hulls()} projected hulls and all their hole thresholds, "
          f"{check_tables()} monomial parities, {check_one_point_repairs()} one-point "
          f"repairs, {check_two_holes()} two-hole pairs, "
          f"{check_closed_circuits()} tagged circuit assignments and "
          f"{check_native_logs()} CPU-consistent small logs.")
