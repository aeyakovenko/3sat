"""Exact searches for short parity refutations after low-weight repairs."""

from itertools import combinations, product
from random import Random


def span(generators):
    values = {0}
    for column in generators:
        values.update([v ^ column for v in values])
    return frozenset(values)


def subspaces(generators):
    spaces = {frozenset({0})}
    for column in generators:
        spaces.update([frozenset(space | {v ^ column for v in space}) for space in spaces])
    return spaces


def components(repairs, size):
    adjacent = [set() for _ in range(size)]
    ground = set()
    for column in repairs:
        support = [i for i in range(size) if column >> i & 1]
        if len(support) == 1:
            ground.update(support)
        elif len(support) == 2:
            i, j = support
            adjacent[i].add(j)
            adjacent[j].add(i)
    seen = set()
    result = []
    for start in range(size):
        if start in seen:
            continue
        pending = [start]
        part = set()
        while pending:
            i = pending.pop()
            if i not in part:
                part.add(i)
                pending.extend(adjacent[i] - part)
        if not (part & ground):
            result.append(sum(1 << i for i in part))
        seen.update(part)
    return result


def parity(mask, value):
    return (mask & value).bit_count() % 2


def small_refutation(code, target, parts, cap):
    """Row elimination retains the original row mask of every derived equation."""
    pivots = {}
    for part in parts:
        if part.bit_count() > cap:
            continue
        row = sum(parity(part, word) << j for j, word in enumerate(sorted(code)))
        charge = parity(part, target)
        mask = part
        while row:
            lead = row.bit_length() - 1
            if lead not in pivots:
                pivots[lead] = (row, charge, mask)
                break
            other, rhs, origin = pivots[lead]
            row ^= other
            charge ^= rhs
            mask ^= origin
        else:
            if charge:
                return mask
    raise AssertionError("short components should be inconsistent")


def weight_table(weights):
    return [sum(w for i, w in enumerate(weights) if mask >> i & 1)
            for mask in range(1 << len(weights))]


def verify_spaces(size, weights_list):
    space_list = subspaces(range(1, 1 << size))
    low = [i for i in range(1, 1 << size) if i.bit_count() <= 2]
    repair_spaces = subspaces(low)
    targets = range(1 << size)
    weight_tables = [weight_table(weights) for weights in weights_list]
    cases = produced = 0
    for repairs in repair_spaces:
        parts = components(repairs, size)
        assert {v for v in targets if not any(parity(row, v) for row in parts)} == repairs
        generators = [x for x in low if x in repairs]
        for code in space_list:
            common = code & repairs
            s = len(repairs).bit_length() - len(common).bit_length()
            t = len(code).bit_length() - len(common).bit_length()
            relaxed = {x ^ y for x in code for y in repairs}
            assert len(relaxed) == len(code) << s
            for weights, costs in zip(weights_list, weight_tables):
                enlarged = set(code)
                penalty = 0
                for g in sorted(generators, key=costs.__getitem__):
                    if g not in enlarged:
                        enlarged.update([x ^ g for x in enlarged])
                        penalty += costs[g]
                assert relaxed == enlarged
                if all(w == 1 for w in weights):
                    assert penalty <= 2 * s
                for target in targets:
                    dist = min(costs[target ^ x] for x in code)
                    relaxed_dist = min(costs[target ^ x] for x in relaxed)
                    assert relaxed_dist >= dist - penalty
                    if dist > penalty:
                        cap = sum(weights) // (dist - penalty)
                        mask = small_refutation(code, target, parts, cap)
                        assert mask.bit_count() <= (t+1) * cap
                        assert parity(mask, target) and all(not parity(mask, v) for v in code)
                        produced += 1
                    cases += 1
    return cases, produced


def minimum_core(rows):
    for size in range(1, len(rows)+1):
        for chosen in combinations(rows, size):
            total = 0
            for row in chosen:
                total ^= row
            if total == 1:
                return size
    return None


def subdivide(rows, length):
    result = []
    fresh = max(row.bit_length() for row in rows)
    for row in rows:
        incoming = 0
        for j in range(length):
            outgoing = 0 if j+1 == length else 1 << fresh
            if outgoing:
                fresh += 1
            result.append((row if j == 0 else 0) ^ incoming ^ outgoing)
            incoming = outgoing
    return result


def audit_chains():
    rng = Random(382)
    count = 0
    for rows in [[1], [2, 3], [2, 4, 7], [2, 4, 8, 15]] + [
        [rng.randrange(16) for _ in range(4)] for _ in range(45)
    ]:
        base = minimum_core(rows)
        for size in range(1, 5):
            new = subdivide(rows, size)
            expected = None if base is None else base * size
            assert minimum_core(new) == expected
            old_bits = max(row.bit_length() for row in rows)
            for original in product((0, 1), repeat=max(0, old_bits-1)):
                assignment = sum(bit << (j+1) for j, bit in enumerate(original))
                for i, row in enumerate(rows):
                    chain = new[i*size:(i+1)*size]
                    private = sorted({bit for q in chain for bit in range(old_bits, q.bit_length())
                                      if q >> bit & 1})
                    best = min(sum(parity(q, assignment | private_value | 1) for q in chain)
                               for private_value in (sum(bit << j for j, bit in zip(private, values))
                                                     for values in product((0, 1), repeat=len(private))))
                    assert best == parity(row, assignment | 1)
            count += 1
    return count


if __name__ == "__main__":
    cases = witnesses = 0
    for size in range(1, 5):
        totals = verify_spaces(size, [[1]*size, list(range(1, size+1)), [i % 3 for i in range(size)]])
        cases += totals[0]
        witnesses += totals[1]
    print(f"{cases} code, repair space, weights, and target combinations through four rows")
    print(f"{witnesses} constructed contradictions passed the exact rank and distance bound")
    print(f"{audit_chains()} row subdivisions preserved optimum and scaled minimum core size")
