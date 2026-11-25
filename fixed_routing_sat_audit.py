"""Beneš routing, anchored SAT controls, and direct finite audits (standard library)."""

from dataclasses import dataclass, replace
from itertools import permutations, product
from random import Random


def switch_count(r):
    if r < 1 or r & (r - 1):
        raise ValueError("lane count must be a positive power of two")
    return (r // 2) * (2 * (r.bit_length() - 1) - 1)


def inverse(permutation):
    result = [None] * len(permutation)
    for i, j in enumerate(permutation):
        if not 0 <= j < len(result) or result[j] is not None:
            raise ValueError("invalid permutation")
        result[j] = i
    return tuple(result)


def route(permutation):
    """Encode a left-to-right permutation by two-coloring its alternating cycles."""
    r = len(permutation)
    settings = [0] * switch_count(r)
    def fill(order, offset):
        size = len(order)
        predecessor = inverse(order)
        if size == 1:
            return
        if size == 2:
            settings[offset] = order[0]
            return

        h = size // 2
        color = [-1] * size
        for start in range(size):
            if color[start] >= 0:
                continue
            color[start] = 0
            pending = [start]
            while pending:
                i = pending.pop()
                # Pair both input ends and both preimages of each output pair.
                for neighbor in (i ^ h, predecessor[order[i] ^ h]):
                    desired = 1 - color[i]
                    if color[neighbor] < 0:
                        color[neighbor] = desired
                        pending.append(neighbor)
                    else:
                        assert color[neighbor] == desired

        inner = switch_count(h)
        final = offset + h + 2 * inner
        sub = [[None] * h for _ in range(2)]
        for i, j in enumerate(order):
            sub[color[i]][i % h] = j % h
        for i in range(h):
            settings[offset + i] = color[i]
            settings[final + i] = color[predecessor[i]]
        fill(sub[0], offset + h)
        fill(sub[1], offset + h + inner)

    fill(permutation, 0)
    return tuple(settings)


def switched(values, settings, offset):
    h = len(values) // 2
    upper, lower = list(values[:h]), list(values[h:])
    for i in range(h):
        if settings[offset + i]:
            upper[i], lower[i] = lower[i], upper[i]
    return tuple(upper), tuple(lower)


def send(values, settings):
    """Evaluate every switch, with no permutation supplied to the evaluator."""
    if len(settings) != switch_count(len(values)):
        raise ValueError("incorrect number of switch bits")

    def run(lanes, offset):
        size = len(lanes)
        if size == 1:
            return tuple(lanes)
        if size == 2:
            return tuple(reversed(lanes)) if settings[offset] else tuple(lanes)
        h = size // 2
        inner = switch_count(h)
        upper, lower = switched(lanes, settings, offset)
        upper = run(upper, offset + h)
        lower = run(lower, offset + h + inner)
        a, b = switched(upper + lower, settings, offset + h + 2 * inner)
        return a + b

    return run(values, 0)


@dataclass(frozen=True)
class Controls:
    settings: tuple
    joined: tuple  # Equalities of adjacent left lanes.
    negative: tuple  # In physical clause-slot order, three signs per right port.
    enabled: tuple
    pins: tuple  # None, 0 or 1 at each right port.


def right_passes(values, c):
    for i, enabled in enumerate(c.enabled):
        port = 4 * i
        if c.pins[i] is not None and values[port] != c.pins[i]:
            return False
        if enabled and not any(values[port + j + 1] != c.negative[3 * i + j]
                               for j in range(3)):
            return False
    return True


def accepts_left(left, c):
    for i, join in enumerate(c.joined):
        if join and left[i] != left[i + 1]:
            return False
    return right_passes(send(left, c.settings), c)


def left_names(c):
    names = [0]
    for join in c.joined:
        names.append(names[-1] if join else names[-1] + 1)
    return tuple(names)


def implicit_formula(c):
    """Reconstruct a CNF on left equality groups for arbitrary physical controls."""
    left = left_names(c)
    right = send(left, c.settings)
    clauses = []
    for i, enabled in enumerate(c.enabled):
        port = 4 * i
        if c.pins[i] is not None:
            var = right[port] + 1
            clauses.append((var if c.pins[i] else -var,))
        if enabled:
            clause = tuple((right[port + j + 1] + 1) * (-1 if c.negative[3 * i + j] else 1)
                           for j in range(3))
            clauses.append(clause)
    return left[-1] + 1, tuple(clauses)


def cnf_passes(clauses, assignment):
    return all(any(assignment[abs(lit) - 1] != (lit < 0) for lit in clause)
               for clause in clauses)


def from_cnf(n, clauses, pins=None):
    """Right lanes 4i..4i+3 are variable port i and the i-th clause triple."""
    if n < 0 or any(len(row) != 3 or any(not 1 <= abs(v) <= n for v in row)
                    for row in clauses):
        raise ValueError("signed literals must be in 1..n and all clauses ternary")
    pins = tuple([None] * n if pins is None else pins)
    if len(pins) != n or any(p not in (None, 0, 1) for p in pins):
        raise ValueError("invalid external pins")
    t = 1 << (max(1, n, len(clauses)) - 1).bit_length()
    names = []
    signs = []
    for i in range(t):
        names.append(i)
        row = clauses[i] if i < len(clauses) else (1, 1, 1)
        names.extend(abs(v) - 1 for v in row)
        signs.extend(int(v < 0) for v in row)
    permutation = sorted(range(4 * t), key=lambda index: names[index])
    sorted_names = [names[j] for j in permutation]
    joined = tuple(a == b for a, b in zip(sorted_names, sorted_names[1:]))
    return Controls(route(permutation), joined, tuple(signs),
                    tuple(i < len(clauses) for i in range(t)), pins + (0,) * (t - n))


def compose(first, second):
    """Keep both halves' inner settings and set each of the two new layers straight."""
    h = len(first.joined) + 1
    if h != len(second.joined) + 1:
        raise ValueError("components must have the same size")
    return Controls((0,) * h + first.settings + second.settings + (0,) * h,
                    first.joined + (False,) + second.joined,
                    first.negative + second.negative,
                    first.enabled + second.enabled, first.pins + second.pins)


def all_bits(n):
    return product((0, 1), repeat=n)


def test_routing():
    for r in (1, 2, 4, 8):
        lanes = tuple(range(r))
        for permutation in permutations(lanes):
            assert send(lanes, route(permutation)) == inverse(permutation)
    decoded = {send(tuple(range(4)), settings) for settings in all_bits(switch_count(4))}
    assert decoded == set(permutations(range(4)))


def test_anchored():
    cases = [(0, ()), (1, ((1, -1, 1),)), (2, ((1, 1, 1), (-1, -1, -1))),
             (2, ((1, -2, 1), (-1, 2, -1))), (3, ((-1, 2, 1),)),
             (3, ((-1, -1, 2), (-2, 3, 1), (-2, 3, 1)))]
    for n, clauses in cases:
        for pins in product((None, 0, 1), repeat=n):
            c = from_cnf(n, clauses, pins)
            names = left_names(c)
            free, reconstructed = implicit_formula(c)
            projected = []
            for assignment in all_bits(free):
                left = tuple(assignment[k] for k in names)
                accepted = accepts_left(left, c)
                assert accepted == cnf_passes(reconstructed, assignment)
                if accepted:
                    projected.append(send(left, c.settings)[::4][:n])
            expected = {a for a in all_bits(n) if cnf_passes(clauses, a)
                        and all(p is None or p == b for p, b in zip(pins, a))}
            assert len(projected) == len(set(projected)) and set(projected) == expected
        for i, clause in enumerate(clauses):
            for j in range(3):
                changed = list(clauses)
                changed[i] = tuple(-v if k == j else v for k, v in enumerate(clause))
                changed_control = from_cnf(n, changed)
                c = from_cnf(n, clauses)
                signs = list(c.negative)
                signs[3 * i + j] ^= 1
                assert changed_control == replace(c, negative=tuple(signs))


def test_arbitrary_controls():
    random = Random(917)
    def controls(settings):
        return Controls(settings, tuple(random.randrange(2) for _ in range(3)),
                        tuple(random.randrange(2) for _ in range(3)), (random.randrange(2),),
                        (random.choice((None, 0, 1)),))

    for settings in all_bits(switch_count(4)):
        a = controls(settings)
        b = controls(tuple(random.randrange(2) for _ in settings))
        ab = compose(a, b)
        groups, formula = implicit_formula(ab)
        names = left_names(ab)
        for left in all_bits(8):
            expected = accepts_left(left[:4], a) and accepts_left(left[4:], b)
            assert accepts_left(left, ab) == expected
            if all(not ab.joined[i] or left[i] == left[i + 1] for i in range(7)):
                assignment = [left[names.index(k)] for k in range(groups)]
                assert cnf_passes(formula, assignment) == expected


if __name__ == "__main__":
    test_routing()
    test_anchored()
    test_arbitrary_controls()
    print("All permutations through 8 lanes, all 4-lane settings, anchored CNFs,"
          " sign flips, arbitrary controls and doubling passed.")
