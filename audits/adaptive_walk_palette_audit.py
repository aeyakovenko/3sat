"""Check adaptive row and walk edits under whole-column permutations."""

from math import isqrt
from random import Random

from packed_row_queries import mgg_transition


class MaskBuffer:
    """Add packed vectors of signed unit increments to a row of counters."""

    def __init__(self, columns):
        self.columns = columns
        self.scalar = [0] * columns
        self.limit = columns * columns.bit_length()
        self.events = 0
        self.pools = ([], [])
        self.flushes = 0
        self.compressors = 0
        self.total_events = 0

    def add(self, mask, negative):
        if not mask:
            return
        self.events += 1
        self.total_events += 1
        pool = self.pools[negative]
        level = 0
        while level < len(pool) and len(pool[level]) == 2:
            a, b = pool[level]
            pool[level] = [a ^ b ^ mask]
            mask = (a & b) | (a & mask) | (b & mask)
            self.compressors += 1
            level += 1
        if level == len(pool):
            pool.append([])
        pool[level].append(mask)
        if self.events == self.limit:
            self.scalar = [self.get(c) for c in range(self.columns)]
            self.events = 0
            self.pools = ([], [])
            self.flushes += 1

    def get(self, column):
        value = self.scalar[column]
        for pool, sign in zip(self.pools, (1, -1)):
            for j, masks in enumerate(pool):
                value += sign * sum(((m >> column) & 1) << j for m in masks)
        return value


def walk(columns, seed):
    start, steps = seed
    points = [start]
    for step in steps:
        points.append(mgg_transition(columns, points[-1], step))
    return points


class CrossCounts:
    def __init__(self, columns, masks, seeds):
        self.columns = columns
        self.bits = (1 << columns) - 1
        self.masks = masks[:]
        self.selected = [[walk(columns, seed) for seed in seq] for seq in seeds]
        self.length = len(self.selected[0][0])
        self.visits = [[0] * columns for _ in masks]
        self.counters = [MaskBuffer(columns) for _ in range(columns)]
        self.translations = MaskBuffer(columns)
        side = isqrt(columns)
        self.shifts = [[(b // side + g // side) % side * side + (b % side + g % side) % side
                        for b in range(columns)] for g in range(columns)]
        for blocks in self.selected:
            for z, block in enumerate(blocks):
                for j, value in enumerate(block):
                    self.visit(z * self.length + j, value, 1)
                self.finish_catalogue()

    def change(self, column, mask, negative):
        self.counters[column].add(mask, negative)
        rotated = sum(((mask >> mapping[column]) & 1) << g
                      for g, mapping in enumerate(self.shifts))
        self.translations.add(rotated, negative)

    def finish_catalogue(self):
        # After each local edit, all later translations use a direct scalar lookup.
        eager = self.translations
        eager.scalar = [eager.get(g) for g in range(self.columns)]
        eager.pools = ([], [])
        eager.events = 0

    def visit(self, row, column, amount):
        before = self.visits[row][column]
        after = before + amount
        assert after >= 0
        self.visits[row][column] = after
        if bool(before) != bool(after):
            self.change(column, self.bits ^ self.masks[row], after == 0)

    def replace_seed(self, query, group, seed):
        new = walk(self.columns, seed)
        old = self.selected[query][group]
        for j, (a, b) in enumerate(zip(old, new)):
            if a != b:
                self.visit(group * self.length + j, a, -1)
                self.visit(group * self.length + j, b, 1)
        self.selected[query][group] = new
        self.finish_catalogue()

    def replace_mask(self, row, new):
        old = self.masks[row]
        for c, count in enumerate(self.visits[row]):
            if count:
                self.change(c, old & ~new, False)
                self.change(c, new & ~old, True)
        self.masks[row] = new
        self.finish_catalogue()

    def all_good(self, mapping):
        return all(self.counters[b].get(c) == 0 for b, c in enumerate(mapping))


def check(columns, rounds, rng):
    k, d, q = 16, 4, 7
    steps = [0, 1, 2, 3, 7, 8, 15, 0x32, 0x54]

    def seed():
        return rng.randrange(columns), [rng.choice(steps) for _ in range(d - 1)]

    def mask():
        return sum(1 << c for c in rng.sample(range(columns), columns // 2))

    masks = [mask() for _ in range(k)]
    seeds = [[seed() for _ in range(k // d)] for _ in range(q)]
    data = CrossCounts(columns, masks, seeds)
    perm = list(range(columns))
    for t in range(rounds):
        direct = [[0] * columns for _ in range(columns)]
        for i, rowmask in enumerate(masks):
            occupied = {walk(columns, seq[i // d])[i % d] for seq in seeds}
            for b in occupied:
                for c in range(columns):
                    direct[b][c] += int(not (rowmask & (1 << c)))
        assert all(data.counters[b].get(c) == direct[b][c]
                   for b in range(columns) for c in range(columns))
        assert data.translations.scalar == [
            sum(direct[b][c] for b, c in enumerate(mapping)) for mapping in data.shifts]
        # Noninjective maps and both shift axes are also legal views.
        u = isqrt(columns)
        h = rng.randrange(columns)
        shift = [(b // u + h // u) % u * u + (b % u + h % u) % u for b in range(columns)]
        maps = [perm, shift, [rng.randrange(columns) for _ in perm]]
        for view in maps:
            assert data.all_good(view) == all(direct[b][c] == 0 for b, c in enumerate(view))
        # The chosen update may depend on an answer just produced.
        choice = (int(data.all_good(perm)) + rng.randrange(3)) % 3
        if choice == 0:
            row = rng.randrange(k)
            visible = mask()
            masks[row] = sum(((visible >> b) & 1) << perm[b] for b in range(columns))
            assert all((masks[row] >> perm[b]) & 1 == (visible >> b) & 1
                       for b in range(columns))
            data.replace_mask(row, masks[row])
        elif choice == 1:
            j, z = rng.randrange(q), rng.randrange(k // d)
            seeds[j][z] = seed()
            data.replace_seed(j, z, seeds[j][z])
        else:
            rng.shuffle(perm)
    assert all(row.compressors <= row.total_events for row in data.counters)
    assert sum(row.flushes for row in data.counters) > 0


def main():
    rng = Random(86951)
    for columns in (4, 16):
        check(columns, 350, rng)
    # The same constant walks can change all selected answers in one global move.
    columns = 4
    data = CrossCounts(columns, [3] * 8, [[(b, [0x8] * 3)] * 2 for b in (0, 1)])
    assert data.all_good([0, 1, 2, 3])
    assert not data.all_good([2, 3, 0, 1])
    print("700 adaptive states checked against all cross counts, with positive and negative "
          "flushes, translations and general maps; one permutation flips every selected bit.")


if __name__ == "__main__":
    main()
