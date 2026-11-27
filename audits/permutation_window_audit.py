"""Compare sparse sign-and-collision defects with all compatible permutations."""
from functools import lru_cache
from itertools import combinations, permutations, product
from random import Random


@lru_cache(None)
def signs(n):
    return {p: sum(a > b for a, b in combinations(p, 2)) % 2
            for p in permutations(range(n))}


def final_table(p, maps, patch):
    return tuple(patch[i] if i in patch else row[p[i]] for i, row in enumerate(maps))


def ground_truth(maps, pins, patch, start, end):
    table = signs(len(maps))
    return any(table.get(final_table(p, maps, patch)) != end
               for p, sign in table.items()
               if sign == start and all(p[i] == v for i, v in pins.items()))


def sparse_defect(maps, pins, patch, start, end):
    n = len(maps)
    assert patch.keys() <= pins.keys()
    if len(set(pins.values())) != len(pins):
        return False
    free = [i for i in range(n) if i not in pins]
    unused = sorted(set(range(n)) - set(pins.values()))
    if len(free) < 4:
        for residual in permutations(unused):
            p = dict(pins)
            p.update(zip(free, residual))
            old = tuple(p[i] for i in range(n))
            if signs(n)[old] == start and signs(n).get(final_table(old, maps, patch)) != end:
                return True
        return False

    # Only two extra old values are needed to witness a collision.
    options = [[pins[i]] if i in pins else unused for i in range(n)]
    for i, j in combinations(range(n), 2):
        for v in options[i]:
            for w in options[j]:
                if v != w and patch.get(i, maps[i][v]) == patch.get(j, maps[j][w]):
                    return True

    g = maps[free[0]]
    before = [g[pins[i]] for i in pins]
    after = [patch.get(i, maps[i][pins[i]]) for i in pins]
    if sorted(before) != sorted(after):
        return True
    # Ranks relative to the same sorted alphabet identify the finite patch.
    ordered = sorted(before)
    transfer = dict(zip(before, after))
    patch_perm = tuple(ordered.index(transfer[v]) for v in ordered)
    return start ^ signs(n)[g] ^ signs(len(pins))[patch_perm] != end


def check(maps, pins, patch, start, end):
    observed = sparse_defect(maps, pins, patch, start, end)
    expected = ground_truth(maps, pins, patch, start, end)
    assert observed == expected, (maps, pins, patch, start, end, observed, expected)


def check_small_support():
    total = 0
    for n in range(2, 8):
        table = signs(n)
        rng = Random(450 + n)
        for _ in range(80):
            original = rng.choice(list(table))
            selected = rng.sample(range(n), rng.randrange(n + 1))
            pins = {i: original[i] for i in selected}
            m = len(pins)
            feasible = [p for p in table if table[p] == table[original]
                        and all(p[i] == v for i, v in pins.items())]
            minimum = min(sum(i != v for i, v in enumerate(p)) for p in feasible)
            assert minimum <= max(2*m, m+2)
            total += 1
    print(f"{total} prescribed-sign support bounds checked")


def switch_edges(bits):
    layers = [(2*i+b, 2*(i+1)+(b^x))
              for i, x in enumerate(bits) for b in range(2)]
    return layers + [(2*len(bits), 0)]


def even(table):
    assert sorted(table) == list(range(len(table)))
    return sum(a > b for a, b in combinations(table, 2)) % 2 == 0


def switches_admit_activation(bits):
    edges = switch_edges(bits)
    # Each other edge is absent or points in one of its two directions.
    for orientations in product(range(3), repeat=len(edges)-1):
        used = [(a, b) if direction == 1 else (b, a)
                for (a, b), direction in zip(edges[:-1], orientations) if direction]
        used.append(edges[-1])
        tails, heads = zip(*used)
        if len(set(tails)) == len(tails) and sorted(tails) == sorted(heads):
            return True
    return False


def even_tables_for_closed_path(bits):
    edges = switch_edges(bits)
    first_edge = 2*(len(bits)+1)
    cells = 1 << (first_edge + len(edges) + 1).bit_length()
    p = list(range(cells))
    track = 0
    active = []
    for layer, bit in enumerate(bits):
        active.append(2*layer+track)
        track ^= bit
    assert track == 0
    active.append(len(edges)-1)
    for edge in active:
        address = first_edge + edge
        tail = edges[edge][0]
        p[address], p[tail] = p[tail], p[address]
    if not even(p):
        p[-1], p[-2] = p[-2], p[-1]
    q = p.copy()
    for edge, (tail, head) in enumerate(edges):
        address = first_edge + edge
        if p[address] == tail:
            q[address] = head
        elif p[address] == head:
            q[address] = tail
    assert even(p) and even(q)
    assert p[first_edge+len(edges)-1] == edges[-1][0]
    assert sum(p[i] != i for i in range(cells)) >= len(bits)+1


def check_two_assertions():
    tested = 0
    for size in (2, 4):
        for bits in product(range(2), repeat=size):
            parity_even = sum(bits) % 2 == 0
            assert switches_admit_activation(bits) == parity_even
            if parity_even:
                even_tables_for_closed_path(bits)
            tested += 1
    print(f"All {tested} small switch networks matched XOR, with even-table witnesses")


def main():
    n = 4
    alphabet = list(signs(n))
    # A single checker with n=4 already exercises every collection of row maps.
    for maps in product(alphabet, repeat=n):
        check(maps, {}, {}, 0, 0)
    print(f"All {len(alphabet)**n:,} four-position relabelings passed")

    rng = Random(701)
    tested = 0
    for n in range(2, 8):
        alphabet = list(signs(n))
        for rep in range(100):
            base = rng.choice(alphabet)
            p = rng.choice(alphabet)
            pins = {i: p[i] for i in rng.sample(range(n), rng.randrange(n + 1))}
            maps = [base if rep % 2 == 0 else rng.choice(alphabet) for _ in range(n)]
            patch = {i: rng.randrange(n) for i in pins if rng.randrange(2)}
            if rep % 3 == 0:
                outputs = [maps[i][p[i]] for i in pins]
                rng.shuffle(outputs)
                patch = dict(zip(pins, outputs))
            for start, end in product(range(2), repeat=2):
                check(maps, pins, patch, start, end)
                tested += 1
    print(f"{tested:,} pinned and patched sign tests passed")
    maps = [tuple((2*i-v) % 3 for v in range(3)) for i in range(3)]
    assert not ground_truth(maps, {}, {}, 0, 0)
    assert len(set(maps)) == 3 and signs(3)[maps[0]] == 1
    print("Three free positions can preserve even parity with three different row maps")
    check_small_support()
    check_two_assertions()


if __name__ == "__main__":
    main()
