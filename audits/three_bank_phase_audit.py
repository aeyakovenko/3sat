"""Exhaustively compare three truncated, adaptive replays with a full replay."""

from itertools import combinations, product
from random import Random


def full_replay(program, data, start, goal, horizon, exceptions):
    state = start
    seen = set()
    for time in range(horizon + 1):
        if state == goal:
            return len(seen) < 3
        if time == horizon or program[state] is None:
            return False
        address, on_zero, on_one = program[state]
        if address not in exceptions:
            seen.add(address // 2)
        state = (on_zero, on_one)[data[address]]
    raise AssertionError("horizon")


def visible_replay(program, data, start, goal, horizon, dictionary, missing):
    if any(data[key] != val for key, val in dictionary.items() if key // 2 != missing):
        return False
    state = start
    seen = set()
    for time in range(horizon + 1):
        if state == goal:
            return True
        if time == horizon or program[state] is None:
            return False
        address, on_zero, on_one = program[state]
        bank = address // 2
        if address in dictionary:
            bit = dictionary[address]
        elif bank == missing:
            return len(seen) < 2
        else:
            seen.add(bank)
            bit = data[address]
        state = (on_zero, on_one)[bit]
    raise AssertionError("horizon")


def check_phases():
    rng = Random(91927)
    # A sequential crossing and adaptive programs, including cycles and early halts.
    programs = [
        ((0, 1, 1), (2, 2, 2), (4, 3, 3), None),
        ((1, 1, 3), (4, 3, 2), (2, 3, 0), None),
    ]
    for _ in range(5):
        states = tuple((rng.randrange(6), rng.randrange(4), rng.randrange(4)) for _ in range(3))
        programs.append(states + (None,))
    count = 0
    excluded = 0
    dishonest = 0
    for bits in product(range(2), repeat=6):
        locations = [coords for length in (0, 1, 2) for coords in combinations(range(6), length)]
        for coords in locations:
            dictionary = {i: bits[i] for i in coords}
            for prog in programs:
                for start in range(3):
                    for goal in range(4):
                        wanted = full_replay(prog, bits, start, goal, 6, dictionary)
                        local = [visible_replay(prog, bits, start, goal, 6, dictionary, bank)
                                 for bank in range(3)]
                        assert all(local) == wanted
                        count += 1
                        if not wanted and start != goal and all(
                                visible_replay(prog, bits, start, goal, 6, dict(enumerate(bits)), bank)
                                for bank in range(3)):
                            excluded += 1
            if coords:
                corrupted = dict(dictionary)
                corrupted[coords[0]] ^= 1
                assert not all(visible_replay(programs[0], bits, 0, 0, 0, corrupted, bank)
                               for bank in range(3))
                dishonest += 1
    assert excluded > 0
    return count, excluded, dishonest


def check_cylinders():
    data = list(product(range(2), repeat=3))
    count = 0
    max_abs = 0
    for masks in product(range(16), repeat=3):
        signed_sum = 0
        for a, b, c in data:
            indices = (2 * b + c, 2 * a + c, 2 * a + b)
            if all((mask >> idx) & 1 for mask, idx in zip(masks, indices)):
                signed_sum += (-1) ** (a * b * c)
        max_abs = max(max_abs, abs(signed_sum))
        assert 4 * signed_sum**4 <= 3 * 8**4
        count += 1
    return count, max_abs


def check_signed_agreement():
    # Every truth pattern, including agreeing and disagreeing private encodings.
    labels = range(3)
    signs = list(product((-1, 1), repeat=len(labels)))
    checks = 0
    for a, b, c in product(labels, repeat=3):
        total = sum(u[a] * (u[b] * v[b]) * v[c] for u, v in product(signs, repeat=2))
        assert total == len(signs)**2 * (a == b == c)
        checks += 1
    return checks


def check_actual_crossings():
    checked = 0
    for a, b, c in product(range(4), repeat=3):
        successor = (a, b, c, 3)
        expansion = {}
        for start in range(3):
            state = start
            path = []
            seen = {start}
            while successor[state] not in seen:
                new_state = successor[state]
                path.append((state, new_state))
                expansion[start, new_state] = tuple(path)
                seen.add(new_state)
                state = new_state
        if (0, 3) not in expansion:
            continue
        edges = list(expansion)
        for bits in product((False, True), repeat=len(edges)):
            syndrome = 0
            odd_native = set()
            for use, (first, last) in zip(bits, edges):
                if use:
                    syndrome ^= (1 << first) ^ (1 << last)
                    odd_native.symmetric_difference_update(expansion[first, last])
            if syndrome == (1 << 0) ^ (1 << 3):
                assert set(expansion[0, 3]).issubset(odd_native)
                checked += 1
    return checked


def check_exact_pairs():
    tests = 0
    for n in range(2, 8):
        for entries in product(range(3), repeat=n):
            partners = all(any(j != i and value == entries[j] for j in range(n))
                           for i, value in enumerate(entries))
            no_triple = all(not (entries[i] == entries[j] == entries[k])
                            for i, j, k in combinations(range(n), 3))
            assert (partners and no_triple) == all(entries.count(v) in (0, 2) for v in range(3))
            tests += 1
    return tests


def check_fragment_syndrome():
    # All total successor maps on three states with the designated sink absorbing.
    # Macroedges may skip intermediate states. Every subset is an unordered report.
    checks = 0
    for first, second in product(range(3), repeat=2):
        successor = (first, second, 2)
        paths = set()
        for start in range(3):
            state = start
            for _ in range(3):
                state = successor[state]
                if state != start:
                    paths.add((start, state))
        paths = sorted(paths)
        for bits in product((False, True), repeat=len(paths)):
            syndrome = 0
            for use, (a, b) in zip(bits, paths):
                if use:
                    syndrome ^= (1 << a) ^ (1 << b)
            for start in (0, 1):
                if syndrome == (1 << start) ^ (1 << 2):
                    assert (start, 2) in paths
                checks += 1
    return checks


if __name__ == "__main__":
    phases, excluded, dishonest = check_phases()
    cylinders, maximum = check_cylinders()
    equality_cases = check_signed_agreement()
    fragment_cases = check_fragment_syndrome()
    pair_cases = check_exact_pairs()
    cover_cases = check_actual_crossings()
    print(f"{phases:,} phase replays, including {excluded:,} genuinely reachable goals "
          f"with three unlisted banks; {dishonest:,} false dictionaries rejected")
    print(f"{cylinders:,} cylinder intersections; maximum one-coordinate signed mass {maximum}/8; "
          f"{equality_cases} exact three-list sign identities; {fragment_cases} fragment tests; "
          f"{pair_cases} exact-two occurrence lists; {cover_cases} parity covers of true steps")
