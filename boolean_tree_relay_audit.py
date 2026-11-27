"""Exhaustion of finite Boolean relays, patch ranks, and exact clock capacities."""

from itertools import product


def gate_value(table, values):
    key = 0
    for i, bit in enumerate(values):
        key |= bit << i
    return table >> key & 1


def relay_cases():
    """Arbitrary component bits at every node: the source must differ from the combination somewhere."""
    count = 0
    for arity, depth in ((1, 4), (2, 2), (3, 1)):
        nodes = sum(arity**level for level in range(depth + 1))
        first_leaf = nodes - arity**depth
        for table in range(1 << (1 << arity)):
            for bits in range(1 << (nodes * arity)):
                component = [
                    [bits >> (v * arity + j) & 1 for j in range(arity)] for v in range(nodes)
                ]
                query = [gate_value(table, component[v]) for v in range(nodes)]
                value = query[:]
                for v in reversed(range(first_leaf)):
                    value[v] = gate_value(table, value[arity * v + 1 : arity * v + 1 + arity])
                # Child number j of v is node arity*v+1+j and copies component j of its parent.
                source = [1 - value[0]] + [
                    component[(v - 1) // arity][(v - 1) % arity] for v in range(1, nodes)
                ]
                assert source != query
                count += 1
    return count

def patch_cases():
    count = 0
    for maximum in range(4):
        for true_set in range(1 << maximum):
            subsets = [s for s in range(1 << maximum) if s & true_set == s]
            for verdicts in product((False, True), repeat=len(subsets)):
                true_sat = dict(zip(subsets, verdicts, strict=True))
                decided = False
                for j in range(maximum + 1):
                    witnessed_positive = any(
                        s.bit_count() == j and true_sat[s] for s in subsets
                    )
                    next_count_exists = true_set.bit_count() >= j + 1
                    decided |= witnessed_positive and not next_count_exists
                assert decided == true_sat[true_set]
                count += 1
    return count


def tally_capacity():
    # p=2, q=beta=2/3, a=5/2, beta+theta=3/4, binary exponents.
    entries = 0
    for b in range(8, 257):
        base = 1 << b
        exponents = [b]
        while exponents[-1] ** 4 < base**3:
            exponents.append((5 * exponents[-1] + 1) // 2)
        depth = len(exponents) - 1
        assert 3**depth < base
        for level in range(depth):
            previous, following = exponents[level : level + 2]
            tracks = 3 ** (depth - level)
            assert tracks <= base and following > previous + 1
            for rank in {0, max(0, tracks // 2 - 1), tracks - 1}:
                assert rank // 3 < tracks // 3
                assert 3 * (rank // 3) + rank % 3 == rank
                entries += 1
    return entries


def linear_capacities():
    count = 0
    for arity, guess_factor in product(range(2, 12), (1, 3, 11)):
        h = (arity - 1).bit_length()
        u = h + 16 * h * guess_factor
        for b in (16, 24, 48, 96):
            base = 1 << b
            depth = base // (8 * h)
            bits = guess_factor * base
            assert depth * h <= base // 8
            assert b + u * depth > bits + h * depth + 8 * b
            count += 1
    # Use numeric logarithms of the true endpoints, never allocate their bytes.
    for b in (1 << 12, 1 << 14, 1 << 16):
        base = 1 << b
        u = (b.bit_length() - 1) // 2
        for h in (1, 2, 3):
            depth = base // (8 * h)
            cap = base * u // (32 * h)
            assert b + u * depth > h * depth + cap + b * b
            count += 1
    return count


if __name__ == "__main__":
    print(
        f"{relay_cases()} full trees, {patch_cases()} partial-patch systems, "
        f"{tally_capacity()} unary rank/parent cases, "
        f"{linear_capacities()} exact binary clock comparisons"
    )
