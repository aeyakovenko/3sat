"""Independent small checks of late-clause projections, set pairs and polarity.

All SAT verdicts in this audit are obtained by explicit Boolean assignments.
No SAT solver or nonstandard Python module is required.
"""
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from math import comb
from random import Random


def holds(literal, value):
    bit = (value >> (abs(literal) - 1)) & 1
    return bool(bit) == (literal > 0)


def models(formula, n):
    return tuple(x for x in range(1 << n) if
                 all(any(holds(lit, x) for lit in clause) for clause in formula))


def clause_pool(n, widths):
    return [tuple(v * sign for v, sign in zip(names, signs)) for w in widths
            for names in combinations(range(1, n + 1), w)
            for signs in product((-1, 1), repeat=w)]


def joint_projection(formula, n, r):
    """All consistent partial signed assignments of size at most r with a lift."""
    answer = set()
    for value in models(formula, n):
        true = [i if holds(i, value) else -i for i in range(1, n + 1)]
        for count in range(min(n, r) + 1):
            answer.update(frozenset(lits) for lits in combinations(true, count))
    return answer


def projected_verdict(projection, query):
    return any(frozenset(choice) in projection for choice in product(*query))


def physical_packets():
    """Render complete proper DIMACS bytes, reparse the header and exhaust its models."""
    n, width = 4, 64
    pool = clause_pool(n, [3])
    baselines = [(), (pool[0],), tuple(pool[:5]), tuple(pool[:8]), tuple(pool[::3])]
    sample = [pool[j] for j in (0, 2, 7, 9, 16, 21, 27, 31)]
    total = 0
    for base in baselines:
        for r in range(4):
            projection = joint_projection(base, n, r)
            header = f"p cnf {n} {len(base) + r}\n"
            render = lambda c: " ".join(map(str, (*c, 0))) + "\n"
            first = (header + "".join(map(render, base))).encode()
            first += b" " * (-len(first) % width)
            for query in product(sample, repeat=r):
                tail = "".join(map(render, query)).encode()
                assert len(tail) <= width
                data = first + tail.ljust(width)
                assert len(data) % width == 0 and data[-width:].strip() == tail.strip()
                raw = data.split()
                assert raw[:4] == [b"p", b"cnf", b"4", str(len(base) + r).encode()]
                fields = list(map(int, raw[4:]))
                assert len(fields) == 4 * (len(base) + r)
                clauses = []
                for i in range(0, len(fields), 4):
                    x, y, z, end = fields[i:i + 4]
                    assert end == 0 and len({abs(x), abs(y), abs(z)}) == 3
                    clauses.append((x, y, z))
                assert bool(models(clauses, n)) == projected_verdict(projection, query)
                total += 1
    return total


def sparse_extensions():
    n = 3
    pool = clause_pool(n, [1, 2, 3])
    bases = [()] + [(c,) for c in pool] + list(combinations(pool, 2))
    true_sets = [frozenset(i * sign for i, sign in enumerate(signs, 1) if sign)
                 for signs in product((-1, 0, 1), repeat=n)]
    count = certificates = inactive = 0
    for base in bases:
        present = {abs(lit) for c in base for lit in c}
        valid = models(base, n)
        if valid:
            for i in range(1, n + 1):
                for lit in (i, -i):
                    if not any(holds(lit, x) for x in valid):
                        assert i in present
                        inactive += 1
        for value in valid:
            satisfied = [tuple(lit for lit in c if holds(lit, value)) for c in base]
            for chosen in set(frozenset(x) for x in product(*satisfied)):
                forbidden = {-lit for lit in chosen}
                for required in true_sets:
                    if forbidden.isdisjoint(required):
                        constrained = chosen | required
                        assert any(all(holds(lit, x) for lit in constrained) for x in valid)
                        certificates += 1
            false = {(-i if holds(i, value) else i) for i in present}
            for required in true_sets:
                if false & required:
                    continue
                extended = value
                for lit in required:
                    mask = 1 << (abs(lit) - 1)
                    extended = extended | mask if lit > 0 else extended & ~mask
                assert all(holds(lit, extended) for lit in required)
                assert all(holds(i, extended) == holds(i, value) for i in present)
                assert all(any(holds(lit, extended) for lit in c) for c in base)
                count += 1
    return count, certificates, inactive


def pair_bound(pairs):
    assert all(not d & t for d, t in pairs)
    assert all(d & t for i, (d, _) in enumerate(pairs)
               for j, (_, t) in enumerate(pairs) if i != j)
    weight = sum(Fraction(1, comb(len(d) + len(t), len(t))) for d, t in pairs)
    assert weight <= 1
    return weight


def extremizers():
    count = 0
    for s in range(6):
        for r in range(6):
            universe = frozenset(range(s + r))
            pairs = [(universe - frozenset(t), frozenset(t)) for t in combinations(universe, r)]
            assert len(pairs) == comb(s + r, r) and pair_bound(pairs) == 1
            # False unit pins on d and true unit pins on t give this truth table.
            for i, (d, _) in enumerate(pairs):
                for j, (_, t) in enumerate(pairs):
                    assert d.isdisjoint(t) == (i == j)
            count += 1
    return count


def sampled_diagonals():
    n = 3
    pool = clause_pool(n, [1, 2, 3])
    rng = Random(268241)
    totals = [0] * 5
    for _ in range(100):
        rows = [tuple(rng.sample(pool, rng.randint(1, 4))) for _ in range(8)]
        cols = [tuple(rng.sample(pool, rng.randint(1, 3))) for _ in range(8)]
        row_models = [set(models(f, n)) for f in rows]
        col_models = [set(models(f, n)) for f in cols]
        compatible = [[x & y for y in col_models] for x in row_models]
        choices = []
        for i, row in enumerate(rows):
            for j, col in enumerate(cols):
                if not compatible[i][j]:
                    continue
                witness = min(compatible[i][j])
                hits = [tuple(lit for lit in c if holds(lit, witness)) for c in row]
                certificate = min((frozenset(h) for h in product(*hits)), key=len)
                d = frozenset(-lit for lit in certificate)
                t = frozenset(next(lit for lit in c if holds(lit, witness)) for c in col)
                choices.append((i, j, (d, t)))

        def extend(rest, chosen):
            for h, (i, j, pair) in enumerate(rest):
                new = [*chosen, pair]
                pair_bound(new)
                totals[len(new)] += 1
                if len(new) < 4:
                    extend([x for x in rest[h + 1:]
                            if not compatible[i][x[1]] and not compatible[x[0]][j]], new)
        extend(choices, [])
    assert all(totals[1:4])
    return totals[1:]


def lookup(table, m, address):
    return all((table >> (i * m + v)) & 1 for i, v in enumerate(address))


def split_flags(k, m, r):
    """Truth functions of positive one-hot selectors and the shared lookup baseline."""
    bits = m.bit_length() - 1
    assert 1 << bits == m and 1 <= r <= k * bits
    lengths = [k * bits // r + int(j < (k * bits) % r) for j in range(r)]
    addresses = list(product(range(m), repeat=k))
    chunks = []
    for address in addresses:
        word = sum(v << (bits * i) for i, v in enumerate(address))
        label = []
        for size in lengths:
            label.append(word & ((1 << size) - 1))
            word >>= size
        assert word == 0
        chunks.append(tuple(label))
    # Selecting the r units filters actual baseline witnesses by all r flags.
    assert len(set(chunks)) == m ** k
    matching = [[i for i, candidate in enumerate(chunks)
                 if all(x == y for x, y in zip(candidate, pins))] for pins in chunks]
    total = 0
    for table in range(1 << (k * m)):
        baseline = [lookup(table, m, q) for q in addresses]
        for j, q in enumerate(addresses):
            assert any(baseline[i] for i in matching[j]) == lookup(table, m, q)
            total += 1
    return total


def grouped_negative(k, m):
    groups = [list(range(j, k, 3)) for j in range(min(3, k))]
    g = (k + 2) // 3
    addresses = list(product(range(m), repeat=k))
    targets = [sum(1 << (i * m + v) for i, v in enumerate(q)) for q in addresses]
    flags = {}
    for h, bank_group in enumerate(groups):
        for local in product(range(m), repeat=len(bank_group)):
            flags[h, local] = sum(1 << (i * m + v) for i, v in zip(bank_group, local))
    packets = [[flags[h, tuple(q[i] for i in bank_group)]
                for h, bank_group in enumerate(groups)] for q in addresses]
    for table in range(1 << (k * m)):
        for q, packet in zip(addresses, packets):
            assert any(selected & ~table for selected in packet) == (not lookup(table, m, q))

    # A literal's possible activity on the single-zero baselines is an arbitrary
    # subset. Enumerate every such subset of each target and every 3-piece cover.
    occurrences = {}
    covers = 0
    for target in targets:
        subsets = [target]
        while subsets[-1]:
            subsets.append((subsets[-1] - 1) & target)
        for part in subsets:
            occurrences[part] = occurrences.get(part, 0) + 1
        for three in combinations_with_replacement(subsets, 3):
            if three[0] | three[1] | three[2] == target:
                assert max(x.bit_count() for x in three) >= g
                covers += 1
    for support, used_by in occurrences.items():
        assert used_by == m ** (k - support.bit_count())
        if support.bit_count() >= g:
            assert used_by <= m ** (k - g)
    qualifying = {f for pack in packets for f in pack if f.bit_count() >= g}
    t = k - 3 * (g - 1)
    assert len(qualifying) >= t * m ** g
    # Count forced signed occurrences across rows. General satisfiable CNFs
    # with unsupported signed literals are checked independently above.
    missing = [sum(1 for f in qualifying if not (f >> zero & 1))
               for zero in range(k * m)]
    assert sum(missing) >= (k * m - k) * len(qualifying)
    assert 2 * m * max((value + 1) // 2 for value in missing) >= (m - 1) * m ** g
    return (1 << (k * m)) * m ** k, covers


def balanced_costs():
    """Enumerate all possible query support-size profiles, independent of flag construction."""
    profiles = exact = 0
    for k in range(1, 17):
        for m in range(3, 10):
            g = (k + 2) // 3
            t = k - 3 * (g - 1)
            # Scale f by k*m to avoid rounding in the finite lower bound.
            price = [0] + [(k * m - h) * m ** h for h in range(1, k + 1)]
            lower = t * price[g] + (3 - t) * price[g - 1]
            assert all(price[h + 1] - price[h] >= price[h] - price[h - 1]
                       for h in range(1, k))
            for sizes in combinations_with_replacement(range(k + 1), 3):
                if sum(sizes) >= k:
                    assert sum(price[h] for h in sizes) >= lower
                    profiles += 1
            if k % 3 == 0 or k <= 3:
                expected = (3 * m ** g - m ** (g - 1)) if k % 3 == 0 else k * m - 1
                assert lower == expected * k * m
                groups = [list(range(i, k, 3)) for i in range(min(3, k))]
                entries = sum(m ** len(group) for group in groups)
                largest = max(entries - m ** (len(group) - 1) for group in groups)
                assert largest == expected
                exact += 1
    return profiles, exact


def main():
    physical = physical_packets()
    extended, certificates, inactive = sparse_extensions()
    diagonal = sampled_diagonals()
    sharp = extremizers()
    positive = sum(split_flags(k, m, r) for k, m, r in
                   [(2, 4, 1), (2, 4, 2), (2, 4, 3), (3, 2, 2), (4, 2, 3)])
    negative = [grouped_negative(k, m) for k, m in [(2, 3), (3, 2), (4, 2), (5, 2)]]
    profiles, exact = balanced_costs()
    print(f"{profiles} admissible support-size profiles; {exact} sharp equal-group cases")
    print(f"{physical} aligned DIMACS packets; {extended} sparse extensions; "
          f"{sharp} sharp uniform families")
    print(f"{certificates} sparse certificate extensions; {inactive} forced occurrences")
    print(f"sampled diagonals of sizes 1 to 4: {diagonal}; {positive} positive lookup queries")
    print(f"{sum(x for x, _ in negative)} negative queries; "
          f"{sum(y for _, y in negative)} single-zero three-piece covers")


if __name__ == "__main__":
    main()
