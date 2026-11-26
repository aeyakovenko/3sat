"""Check live-prefix pruning, proper DIMACS switches, and projected witness sets."""
from itertools import combinations, product

from binary_read_sat_trace_audit import parse, satisfiable


def split(points, t):
    assert 3 * t < len(points) <= 6 * t
    return points[:t], points[t:-t], points[-t:]


def selected(points, t, mask, side):
    zero, one, free = split(points, t)
    yes = set(one) | {p for j, p in enumerate(free) if mask >> j & 1}
    return [p for p in points if (p in yes) == side]


def verify_losses(t, q):
    points = list(range(q))
    zero, _, free = split(points, t)
    count = 0
    for model_mask in range(1, 1 << q):
        models = {p for p in points if model_mask >> p & 1}
        lost = not (models - set(zero))
        for tags in range(1 << t):
            left = set(selected(points, t, tags, False))
            right = set(selected(points, t, tags, True))
            assert set(points) == left | right and not left & right
            assert min(len(left), len(right)) >= t
            assert right & set(free) == {p for j, p in enumerate(free) if tags >> j & 1}
            for keep, other in ((left, right), (right, left)):
                assert models & (keep if models & keep else other)
            if lost:
                assert models <= left and not models & right
            count += 1
    return count


class Encoding:
    def __init__(self, pairs):
        self.pairs = [(10 * (j + 1) + 2, 10 * (j + 1) + 3) for j in range(pairs)]
        self.last = self.pairs[-1][-1]
        self.rows = [tuple(-i if bit else i for i, bit in enumerate(a, 1))
                     for a in product(range(2), repeat=3) if a != (0, 0, 1)]
        used = {n for pair in self.pairs for n in pair}
        for n in range(4, self.last + 1):
            if n not in used:
                self.rows.append((-n, 1, 2))
        for lo, hi in self.pairs:
            self.rows.extend([(lo, hi, 1), (-lo, -hi, 1)])

    def fresh(self):
        self.last += 1
        return self.last

    def any_of(self, inputs):
        if not inputs:
            return 1  # pinned false
        prev = inputs[0]
        for x in inputs[1:]:
            y = self.fresh()
            self.rows.extend([(-prev, y, 1), (-x, y, 1), (prev, x, -y)])
            prev = y
        return prev


def emit(prefixes, variables, t, tags, side, source, bank_size):
    cnf = Encoding(t + 1)
    names = [cnf.fresh() for _ in range(variables)]
    states = [cnf.fresh() for _ in prefixes]
    for literals in source:
        cnf.rows.append(tuple(names[abs(x)-1] * (1 if x > 0 else -1) for x in literals))
    cnf.rows.extend((-a, -b, 1) for a, b in combinations(states, 2))
    cnf.rows.append((cnf.any_of(states), 1, 2))
    banks = []
    for l in range(0, len(states), bank_size):
        bank = states[l:l + bank_size]
        entries = [1]
        for mask in range(1, 1 << len(bank)):
            lowbit = mask & -mask
            leaf = bank[lowbit.bit_length() - 1]
            smaller = mask ^ lowbit
            entries.append(leaf if not smaller else cnf.any_of([leaf, entries[smaller]]))
        banks.append(entries)
    for bit, out in enumerate(names):
        parts = []
        for j, entries in enumerate(banks):
            group = prefixes[j * bank_size:(j + 1) * bank_size]
            mask = sum(((p >> bit) & 1) << k for k, p in enumerate(group))
            if mask:
                parts.append(entries[mask])
        if not parts:
            cnf.rows.append((-out, 1, 2))
        else:
            value = cnf.any_of(parts)
            cnf.rows.extend([(-out, value, 1), (out, -value, 1)])
    zero, one, free = split(states, t)
    # Each gate output agrees with the truth-table value at the selected state.
    out = cnf.pairs[-1][1]
    for s in zero:
        cnf.rows.append((-s, -out, 1))
    for s in one:
        cnf.rows.append((-s, out, 1))
    for j, s in enumerate(free):
        tag = cnf.pairs[j][1]
        cnf.rows.extend([(-s, -out, tag), (-s, out, -tag)])
    choices = [tags >> j & 1 for j in range(t)] + [int(side)]
    for pair, value in zip(cnf.pairs, choices):
        cnf.rows.append((pair[value], 1, 2))
    body = ''.join(f'{a} {b} {c} 0\n' for a, b, c in cnf.rows)
    return (f'p cnf {cnf.last} {len(cnf.rows)}\n' + body).encode(), names


def model_count(rows, assigned, nvars):
    if not rows:
        return 1 << (nvars - len(assigned))
    shortest = min(rows, key=len)
    if not shortest:
        return 0
    var = abs(shortest[0])
    assert var not in assigned
    choices = [shortest[0]] if len(shortest) == 1 else [var, -var]
    return sum(model_count([tuple(i for i in row if i != -lit)
                            for row in rows if lit not in row],
                           assigned | {var}, nvars) for lit in choices)


def verify_files(t, prefixes, source, allowed):
    used = max(3, max(prefixes).bit_length())
    anchor = None
    cubes = {}
    for tags, side in product(range(1 << t), range(2)):
        file, names = emit(prefixes, used, t, tags, side, source, bank_size=2)
        cubes[tags, side] = file
        rows = parse(file)
        expect = set(selected(prefixes, t, tags, side)) & set(allowed)
        assert satisfiable(rows) == bool(expect)
        assert model_count(rows, set(), max(abs(i) for row in rows for i in row)) == len(expect)
        # Independently check the projection to every assignment on the source names.
        for word in range(1 << used):
            pins = [(name if word >> j & 1 else -name,) for j, name in enumerate(names)]
            assert satisfiable(pins + rows) == (word in expect)
        if anchor is None:
            anchor = len(file)
        assert len(file) == anchor
    base = cubes[0, 0]
    offsets = []
    for j in range(t + 1):
        flipped = cubes[1 << j, 0] if j < t else cubes[0, 1]
        changes = [(i, a ^ b) for i, (a, b) in enumerate(zip(base, flipped)) if a != b]
        assert len(changes) == 1 and changes[0][1] == 1
        offsets.append(changes[0][0])
    assert len(set(offsets)) == len(offsets)
    for (tags, side), file in cubes.items():
        flips = set(i for i, (a, b) in enumerate(zip(file, base)) if a != b)
        assert flips == {offsets[j] for j in range(t + 1) if (tags | (side << t)) >> j & 1}
    return len(cubes)


def main():
    counts = sum(verify_losses(t, q) for t in (1, 2) for q in range(3 * t + 1, 6 * t + 1))
    # A pinned source can have a first loss; a free source reveals all distinct cuts.
    cubes = 0
    for t, points in ((1, [0, 1, 3, 6]), (2, list(range(7)))):
        for models in ({0}, set(range(8)), {0, 4, 7}):
            source = [tuple(-i if excluded >> (i - 1) & 1 else i for i in (1, 2, 3))
                      for excluded in range(8) if excluded not in models]
            cubes += verify_files(t, points, source, models)
    print(f'{counts} live-set and tag cases; {cubes} proper files with every projected witness checked')


if __name__ == '__main__':
    main()
