"""Check shifted-grid and local group charges on short simultaneous head paths."""

from collections import defaultdict
from fractions import Fraction
from itertools import product


def lattice_paths(dimension, moves):
    origin = (0,) * dimension
    steps = [origin]
    for axis, direction in product(range(dimension), (-1, 1)):
        steps.append(tuple(direction if j == axis else 0 for j in range(dimension)))
    for choices in product(steps, repeat=moves):
        points = [origin]
        for step in choices:
            points.append(tuple(a + b for a, b in zip(points[-1], step)))
        yield tuple(points)


def tile(point, shift, side):
    return tuple((x - s) // side for x, s in zip(point, shift))


def accounting(paths, weights, side, capacity, shift, residue):
    times_by_cube = defaultdict(list)
    primary = []
    remotes = 0
    for t, positions in enumerate(zip(*paths)):
        cubes = [tile(p, shift, side) for p in positions]
        primary.append(cubes[0])
        remotes += sum(cube != cubes[0] for cube in cubes[1:])
        for cube in set(cubes):
            times_by_cube[cube].append(t)

    group_at = {}
    group_cuts = 0
    for cube, times in times_by_cube.items():
        group = 0
        length = 0
        for rank, t in enumerate(times):
            if rank and rank % capacity == residue:
                group_cuts += 1
                group += 1
                length = 0
            group_at[cube, t] = group
            length += 1
            assert length <= capacity

    move_copies = local_copies = 0
    for t in range(1, len(primary)):
        cube = primary[t]
        if cube != primary[t - 1]:
            move_copies += weights[t]
        elif group_at[cube, t] != group_at[cube, t - 1]:
            local_copies += weights[t]
    return remotes, move_copies, local_copies, group_cuts


def verify(paths, side, capacity):
    dimension = len(paths[0][0])
    horizon = len(paths[0])
    # Each profile charges 1+S_t. A deliberately high asymmetric weight tests
    # the absence of a scratch charge at ordinary satellite occurrences.
    weights = [1 + ((7 * t + sum(map(abs, p))) % 5) for t, p in enumerate(paths[-1])]
    motion = sum(weights[t] for t in range(1, horizon) if paths[0][t] != paths[0][t - 1])
    distances = []
    for positions in zip(*paths):
        for satellite in positions[1:]:
            distances.append(sum(abs(x - y) for x, y in zip(positions[0], satellite)))
    clipped = Fraction(sum(min(side, distance) for distance in distances), side)
    bounds = [clipped, Fraction(motion, side), Fraction(sum(weights[1:]), capacity),
              Fraction(len(paths) * horizon, capacity)]
    totals = [0] * len(bounds)
    outcomes = 0
    for shift in product(range(side), repeat=dimension):
        for residue in range(capacity):
            charges = accounting(paths, weights, side, capacity, shift, residue)
            totals = [a + b for a, b in zip(totals, charges)]
            outcomes += 1
    assert all(total <= outcomes * bound for total, bound in zip(totals, bounds))
    return outcomes


def check_parked_symbols():
    # A real two-tape transition can branch jointly on the two scanned bits.
    # The two simulated banks may park, move, and revisit cells independently.
    samples = 0
    for p, q in product(lattice_paths(1, 3), repeat=2):
        for mask in range(8):
            logical = [{}, {}]
            backing = [{}, {}]
            cached = [0, 0]
            state = 0
            for t in range(3):
                here = [p[t], q[t]]
                dest = [p[t+1], q[t+1]]
                actual = [logical[h].get(here[h], 0) for h in range(2)]
                assert actual == cached
                left, right = actual
                state ^= (left & right) ^ ((mask >> t) & 1)
                written = [right ^ state, left ^ right ^ 1]
                for h in range(2):
                    logical[h][here[h]] = written[h]
                    if dest[h] == here[h]:
                        cached[h] = written[h]
                    else:
                        backing[h][here[h]] = written[h]
                        cached[h] = backing[h].get(dest[h], 0)
                    decoded = backing[h].copy()
                    decoded[dest[h]] = cached[h]
                    for addr in set(decoded) | set(logical[h]):
                        assert decoded.get(addr, 0) == logical[h].get(addr, 0)
            samples += 1
    return samples


def check_shared_tape():
    samples = swaps = collisions = 0
    for p, q in product(lattice_paths(1, 3), repeat=2):
        for mask in range(8):
            backing, logical = {}, {}
            cache = {p[0]: 0, q[0]: 0}
            for t in range(3):
                a, b = p[t], q[t]
                nxt_a, nxt_b = p[t + 1], q[t + 1]
                before = {a, b}
                after = {nxt_a, nxt_b}
                if a == b:
                    collisions += 1
                if a != b and (a, b) == (nxt_b, nxt_a):
                    swaps += 1
                assert cache == {addr: logical.get(addr, 0) for addr in before}
                left, right = logical.get(a, 0), logical.get(b, 0)
                bit = (mask >> t) & 1
                # Both instructions read the old words. Head 2 wins a write collision.
                logical[a] = right ^ bit
                logical[b] = left ^ right ^ 1
                updated = {a: cache[b] ^ bit, b: cache[a] ^ cache[b] ^ 1}
                for addr in before - after:
                    backing[addr] = updated[addr]
                cache = {addr: updated[addr] if addr in before else backing.get(addr, 0)
                         for addr in after}
                decoded = backing | cache
                for addr in set(logical) | set(decoded):
                    assert logical.get(addr, 0) == decoded.get(addr, 0)
            samples += 1
    assert swaps and collisions
    return samples


def main():
    samples = outcomes = 0
    lines = list(lattice_paths(1, 2))
    planes = list(lattice_paths(2, 2))
    # In the plane include a third tape returning to the origin independently,
    # so one time can contribute multiple records to the same tile.
    triples = list(product(lines, repeat=3))
    triples.extend((a, b, planes[(i + 2*j) % len(planes)])
                   for i, a in enumerate(planes) for j, b in enumerate(planes))
    for paths in triples:
        for side, capacity in product((2, 3), (1, 2, 3)):
            outcomes += verify(paths, side, capacity)
            samples += 1

    d = 2
    c, s = Fraction(11, 10), Fraction(1, 8)
    omega, beta = Fraction(2, 3), Fraction(4, 5)
    assert (d + 1 + d*s)*c*c == Fraction(1573, 400) < c + d + 1
    assert (1 + omega)*c*c == Fraction(121, 60) < c + 1
    assert beta*c*c == Fraction(121, 125) < 1
    x = Fraction(99, 100)
    side_exponent = (c*s + x)/(d + 1)
    chart_exponents = [c*(1+s) - side_exponent, c*(1+omega) - x,
                       c + d*side_exponent - x, c*beta]
    assert max(chart_exponents) < x/c and c*x**10 < 1
    cache_cases = check_parked_symbols()
    shared_cases = check_shared_tape()
    print(f"{samples} path and parameter combinations, {outcomes} shifts and rank residues, "
          f"{cache_cases} separate-tape and {shared_cases} shared-tape cached runs, "
          "and the planar exponent certificate passed.")


if __name__ == "__main__":
    main()
