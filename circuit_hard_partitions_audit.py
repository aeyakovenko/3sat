"""Finite proper-DIMACS and late-interval audit. Requires pycosat."""
from collections import defaultdict
from functools import lru_cache
from itertools import combinations, permutations, product
from random import Random

from dense_ascii_chunk_circuit_audit import bank_name, sat_from_bytes


@lru_cache(maxsize=None)
def layout(w):
    n, b = 1 << w, (w + 3) // 4
    bound = n << 10
    counter = 34 * 10**b - 1
    clauses = []

    def fresh():
        nonlocal counter
        counter += 1
        return counter

    pad, extra, zero = (fresh() for _ in range(3))
    clauses.append((-zero,))

    def binary_gate(x, y, is_and=False):
        # Signed literals are permitted as gate inputs.
        if x == y:
            return x
        if x == -y:
            return zero if is_and else -zero
        out = fresh()
        if is_and:
            clauses.extend([(-out, x), (-out, y), (out, -x, -y)])
        else:
            clauses.extend([(out, -x), (out, -y), (-out, x, y)])
        return out

    def any_bit(items):
        out = zero
        for x in items:
            out = binary_gate(out, x)
        return out

    def one_hot(items, required):
        seen = zero
        for x in items:
            clauses.append((-seen, -x))
            seen = binary_gate(seen, x)
        if required:
            clauses.append((seen,))

    group = [[fresh() for _ in range(n)] for _ in range(3)]
    for choices in group:
        one_hot(choices, True)
    clauses.extend((-x, -y) for x, y in zip(group[0], group[1]))
    decoded = {}
    for tag in range(10, 34):
        flags = [bank_name(tag, a, b) for a in range(1 << b)]
        one_hot(flags, False)
        if tag >= 18:
            decoded[tag] = [any_bit(x for a, x in enumerate(flags) if a >> pos & 1)
                            for pos in range(b)]

    def number(start):
        return [v for tag in range(start, start + 4) for v in decoded[tag]]

    def leq(x, y):
        # Build from least significant bit. More significant differences win.
        same_or_less = -zero
        for a, c in zip(x, y):
            a_lt_c = binary_gate(-a, c, True)
            a_le_c = binary_gate(-a, c)
            same_or_less = binary_gate(a_lt_c, binary_gate(a_le_c, same_or_less, True))
        clauses.append((same_or_less,))

    left, right, low, high = map(number, (18, 22, 26, 30))
    for where in (left, right):
        leq(low, where)
        leq(where, high)
    assert counter < bound - 1
    strict = []
    for row in clauses:
        assert len(set(map(abs, row))) == len(row)
        fillers = (pad, extra)[:3 - len(row)]
        for signs in product((1, -1), repeat=len(fillers)):
            strict.append(row + tuple(s * f for s, f in zip(signs, fillers)))
    strict.extend((bound - 1, v, bound) for v in range(1, bound - 1))
    suffix = ''.join(f"{a} {c} {d} 0\n" for a, c, d in strict).encode()
    variable_rows = (8 * 2 + 4 * 2 + 8) * 2 * n
    return (f"p cnf {bound} {len(strict) + variable_rows}\n".encode(), suffix,
            group, pad, b)


def encode(w, values, positions, intervals):
    header, body, picks, pad, b = layout(w)
    variable = []

    def link(choice, v, start, count):
        for slot in range(count):
            flag = bank_name(start + slot, (v >> (slot*b)) % (1 << b), b)
            variable.extend(f"{-choice} {flag} {p} 0\n" for p in (pad, -pad))

    for i, val in enumerate(values):
        link(picks[0][i], val, 10, 8)
        link(picks[1][i], val, 10, 8)
    for i, pos in enumerate(positions):
        link(picks[0][i], pos, 18, 4)
        link(picks[1][i], pos, 22, 4)
    for i, (lo, hi) in enumerate(intervals):
        link(picks[2][i], lo, 26, 4)
        link(picks[2][i], hi, 30, 4)
    return header + ''.join(variable).encode() + body


def by_pair(vals, pos, lo, hi):
    return any(vals[i] == vals[j] and lo <= pos[i] <= hi and lo <= pos[j] <= hi
               for i, j in combinations(range(len(vals)), 2))


def last_equal(vals, pos):
    rows = defaultdict(list)
    for v, p in zip(vals, pos):
        rows[p].append(v)
    last = {}
    prefix = []
    highest = -1
    for p in range(len(vals)):
        for v in rows[p]:
            highest = max(highest, last.get(v, -1))
            last[v] = p
        prefix.append(highest)
    return prefix


def main():
    rng = Random(4241)
    w, n = 2, 4
    points = range(n)
    queries = list(product(points, repeat=2))
    cases = 0
    for vals in product(range(2), repeat=n):
        for pos in product(points, repeat=n):
            h = last_equal(vals, pos)
            for lo, hi in queries:
                assert (h[hi] >= lo) == by_pair(vals, pos, lo, hi)
                cases += 1
    print(f"{cases:,} range answers with repeated positions and reversed intervals passed.")

    patterns = set()
    positions = list(permutations(points))
    for pos in positions:
        patterns.add(tuple(any(by_pair(vals, pos, lo, hi) for lo, hi in [(0, 1), (2, 3)])
                           for vals in product(points, repeat=n)))
    assert len(patterns) == 3
    # Each input bit affects only the low ASCII bit of its designated digits.
    def from_words(flat):
        vals, pos, lows, highs = (flat[i*n:(i+1)*n] for i in range(4))
        return encode(w, vals, pos, list(zip(lows, highs)))

    base_words = [0] * (4*n)
    baseline = from_words(base_words)
    union = set()
    marked = bytearray(baseline)
    widths = [2*w]*n + [w]*(3*n)
    random_words = [rng.randrange(1 << size) for size in widths]
    for k, width in enumerate(widths):
        for b in range(width):
            flip = base_words.copy()
            flip[k] = 1 << b
            changed = from_words(flip)
            offsets = {j for j, (u, v) in enumerate(zip(baseline, changed)) if u != v}
            assert len(changed) == len(baseline)
            assert len(offsets) == (4 if k < 2*n else 2)
            assert union.isdisjoint(offsets)
            union.update(offsets)
            for j in offsets:
                assert (baseline[j], changed[j]) == (48, 49)
                if random_words[k] >> b & 1:
                    marked[j] = 49
    assert bytes(marked) == from_words(random_words)
    print(f"All {sum(widths)} data-bit columns match disjoint ASCII digits and superpose.")
    lengths = set()
    verdicts = set()
    for _ in range(48):
        vals = [rng.randrange(n) for _ in points]
        pos = [rng.randrange(n) for _ in points]
        selected = rng.choices(queries, k=n)
        file = encode(w, vals, pos, selected)
        actual = sat_from_bytes(file)
        assert actual == any(by_pair(vals, pos, lo, hi) for lo, hi in selected)
        lengths.add(len(file))
        verdicts.add(actual)
    assert len(lengths) == 1 and verdicts == {False, True}
    print(f"All 24 permutations give precisely 3 different two-block functions.")
    print(f"48 dense proper PicoSAT instances passed at one physical length of {lengths.pop():,} bytes.")


if __name__ == "__main__":
    main()
