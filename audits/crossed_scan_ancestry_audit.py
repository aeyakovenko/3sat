"""Audit the last-writer bound at all prefixes of small cyclic scans."""
from fractions import Fraction
from itertools import permutations, product
from random import Random


def audit(initial, successor, start, delta, turns, random_choices=None):
    orbit = [start]
    while successor[orbit[-1]] != start:
        orbit.append(successor[orbit[-1]])
    period = len(orbit)
    palette = set(initial)
    neighborhood = set(palette)
    memory = list(initial)
    destinations = set()
    writers = {}
    events = []
    for i in range(turns * period):
        passes = 1 + i // period
        if i % period == 0:
            neighborhood.update(successor[a] for a in tuple(neighborhood))
        p = orbit[i % period]
        x = memory[p]
        origin = i
        depth = 0
        ancestor = writers.get(p)
        while ancestor is not None:
            assert ancestor < origin
            old_p, old_x, earlier, old_delta = events[ancestor]
            assert (old_x, successor[old_p] if old_delta else old_p) == (p, x)
            origin, p, x = ancestor, old_p, old_x
            ancestor = earlier
            depth += 1
        assert x in palette
        if random_choices is not None:
            assert (i - origin) >= (depth // 2) * period
            assert (depth + 1) // 2 <= passes
        elif delta:
            assert (i - origin) >= (depth // 2) * (period + 1)
            assert (depth + 1) // 2 <= passes

        p = orbit[i % period]
        x = memory[p]
        assert p in neighborhood or x in neighborhood
        if not delta and random_choices is None:
            assert p in palette or x in palette
        write_delta = delta if random_choices is None else random_choices.randrange(-1, 2)
        events.append((p, x, writers.get(p), write_delta))
        if write_delta >= 0:
            writers[x] = i
            memory[x] = successor[p] if write_delta else p
            destinations.add(x)
        assert len(destinations) <= (passes + 1)**2 * len(palette)


def check_triangular_schedule(passes):
    roots = [(i - 1) * (passes + 1) for i in range(1, passes + 1)]
    initial = passes * (passes + 1)
    period = initial + passes + 1
    memory = [initial] * period
    destinations = set()

    for j in range(1, passes + 1):
        expected_read = {}
        for i in range(1, j + 1):
            s = j - i
            root = roots[i - 1]
            expected_read[root + s] = initial + s
            expected_read[initial + s] = root + s + 1
        for address in range(period):
            x = memory[address]
            if address in expected_read:
                assert x == expected_read[address]
                memory[x] = (address + 1) % period
                destinations.add(x)
        # Verify all cells after each pass, including those never visited by a write.
        outside = {roots[i - 1] + s for i in range(1, j + 1) for s in range(1, j - i + 2)}
        changed = {a for a, x in enumerate(memory) if x != initial}
        assert destinations == changed == outside | set(range(initial, initial + j))
        assert len(outside) == j * (j + 1) // 2


def main():
    count = 0
    for size in range(1, 5):
        for successor in permutations(range(size)):
            for initial in product(range(size), repeat=size):
                for start in range(size):
                    for delta in (0, 1):
                        audit(initial, successor, start, delta, 3)
                        count += 1
    rng = Random(54321)
    for _ in range(250):
        size = rng.randrange(8, 100)
        successor = list(range(size))
        rng.shuffle(successor)
        palette = rng.sample(range(size), rng.randint(1, 5))
        initial = rng.choices(palette, k=size)
        start = rng.randrange(size)
        audit(initial, successor, start, rng.randrange(2), 12)
        audit(initial, successor, start, None, 12, rng)
    for period in range(2, 101):
        memory = [1] * period
        destinations = set()
        for i in range(period):
            x = memory[i]
            assert x == (i + 1) % period
            memory[x] = (i + 2) % period
            destinations.add(x)
        assert len(destinations) == period and memory.count(1) == 1
    for passes in range(1, 65):
        check_triangular_schedule(passes)
    c = Fraction(1101, 1000)
    d = ((c + 2) / c**2 - c) / 2
    assert d > Fraction(728, 1000)
    print(f'{count} exhaustive scans, 250 fixed and 250 adaptive random scans passed')
    print('Exact quadratic destination counts checked for every prefix pass through 64 passes')
    print('All 99 offset-two counterexamples wrote the entire orbit')
    print(f'FLMV Corollary 5.8 gives d = {float(d):.9f} at c = {float(c)}')


if __name__ == '__main__':
    main()
