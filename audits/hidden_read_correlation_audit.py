"""Check correlation certificates against every compatible word on small cubes."""
from itertools import product


def bit(a, b):
    return (a & b).bit_count() & 1


def sign(value):
    return 1 - 2 * value


def walsh(values):
    transformed = list(values)
    step = 1
    while step < len(transformed):
        for start in range(0, len(transformed), 2 * step):
            for i in range(start, start + step):
                low, high = transformed[i], transformed[i + step]
                transformed[i], transformed[i + step] = low + high, low - high
        step *= 2
    return transformed


def subspaces(q):
    spaces = {frozenset([0])}
    for x in range(1, q):
        spaces |= {space | {y ^ x for y in space} for space in spaces}
    return spaces


def affine_cells(q, space):
    """Every possible set of hidden words with the same observed character."""
    classes = {}
    for a in range(q):
        answers = tuple(bit(a, x) for x in sorted(space))
        classes.setdefault(answers, []).append(a)
    return classes.values()


def sharp_center(q, space, hidden_example):
    known_phase = [sign(bit(hidden_example, x)) for x in range(q)]
    if len(space) == 1:
        return [1] * q
    values = known_phase.copy()
    assigned = set(space)
    for representative in range(q):
        if representative in assigned:
            continue
        coset = sorted(representative ^ x for x in space)
        assigned.update(coset)
        for x in coset[:len(space) // 2]:
            values[x] = -values[x]
    return values


def check_all_small_centers():
    checks = 0
    for q in (2, 4, 8):
        tables = [walsh(values) for values in product((-1, 1), repeat=q)]
        for space in subspaces(q):
            bound = (q - len(space) + 1) // 2
            for cell in affine_cells(q, space):
                trial = walsh(sharp_center(q, space, cell[0]))
                assert max((q - trial[a]) // 2 for a in cell) == bound
                for coeff in tables:
                    assert sum(coeff[a] ** 2 for a in cell) <= q*q
                    assert max((q - coeff[a]) // 2 for a in cell) >= bound
                    for cut in range(1, q + 1):
                        heavy = sum(abs(coeff[a]) >= cut for a in cell)
                        assert heavy * cut * cut <= q*q
                    checks += 1
    return checks


def quadratic(value, pairs):
    return sum((value >> (2 * i)) & (value >> (2 * i + 1)) & 1
               for i in range(pairs)) & 1


def cylinder(q, first, capacity):
    """A modulated quadratic center for consecutive aligned low-bit frequencies."""
    free_bits = capacity.bit_length() - 1
    prefix = first >> free_bits
    values = [sign(bit(prefix, x >> free_bits) ^ quadratic(x, free_bits // 2))
              for x in range(q)]
    coeff = walsh(values)
    for u, c in enumerate(coeff):
        if first <= u < first + capacity:
            assert c*c * capacity == q*q
        else:
            assert c == 0
    return coeff


def check_lists():
    checks = 0
    for q in (1, 4, 16, 64):
        powers = [4 ** i for i in range((q.bit_length() - 1) // 2 + 1)]
        for counts in product(*(range(min(5, q // p) + 2) for p in powers)):
            capacities = sorted((p for p, n in zip(powers, counts) for _ in range(n)),
                                reverse=True)
            start = 0
            for size in capacities:
                if start == q:
                    break
                assert start % size == 0
                assert start + size <= q
                cylinder(q, start, size)
                start += size
            assert (start == q) == (sum(capacities) >= q)
            checks += 1
    return checks


def check_perturbations():
    checked = 0
    for k in range(1, 6):
        q = 1 << (2*k)
        baseline = [sign(quadratic(x, k)) for x in range(q)]
        altered = baseline.copy()
        altered[3] *= -1
        actual = walsh(altered)
        for a, value in enumerate(actual):
            wanted = (1 << k) * sign(quadratic(a, k)) - 2*sign(1 ^ bit(a, 3))
            assert wanted == value
            assert abs(value) in ((1 << k) - 2, (1 << k) + 2)
            checked += 1
        assert actual[0] == (1 << k) + 2
    return checked


def check_adaptive_paths():
    checked = 0
    for h in range(2, 7):
        q = 1 << h
        for start in range(q):
            def path(hidden):
                probes = []
                x = start
                for i in range(h + 1):
                    answer = bit(hidden, x)
                    probes.append((x, answer))
                    x = (start + x * (2 + answer) + i + answer) % q
                return tuple(probes)
            paths = [path(a) for a in range(q)]
            for transcript in set(paths):
                cell = {a for a in range(q) if paths[a] == transcript}
                expected = {a for a in range(q) if all(bit(a, x) == b for x, b in transcript)}
                assert cell == expected
                checked += 1
    return checked


def check_trial_clocks():
    checked = 0
    for j in range(2, 45):
        m = 1 << j
        active = (2 + ((j + 4).bit_length() - 1)).bit_length() - 1
        for e in range(active):
            native_cap = m >> (e + 1)
            for guest_cost in {1, max(1, native_cap // 2), native_cap}:
                for training in {1, max(1, m // (active + 1) // 5), m}:
                    needed = max((e + 1) ** 2 * guest_cost, (active + 1) * training)
                    budget = 1 << (needed - 1).bit_length()
                    assigned = [min(m >> (rank + 1), budget // (rank + 1) ** 2)
                                for rank in range(active)]
                    assert assigned[e] >= guest_cost
                    assert budget // (active + 1) >= training
                    assert sum(assigned) <= 2 * budget
                    checked += 1
    return checked


if __name__ == "__main__":
    print(f"{check_all_small_centers()} center/coset energy and Hamming tests")
    print(f"{check_lists()} dyadic list capacities checked")
    print(f"{check_perturbations()} one-coordinate bent perturbation coefficients")
    print(f"{check_adaptive_paths()} adaptive transcript cells")
    print(f"{check_trial_clocks()} native guest/training budget checks")
