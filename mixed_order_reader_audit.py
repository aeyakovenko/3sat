"""Compare dynamic last-reset decision, mod-three counts, and witnesses to brute force."""

from itertools import product
from random import Random

from fixed_order_witness_reader_audit import step


# A missing column means unreachable. A present column may have residue zero.
def compose(left, right):
    rows = []
    for row in left:
        result = {}
        for mid, a in row.items():
            for end, b in right[mid].items():
                result[end] = (result.get(end, 0) + a * b) % 3
        rows.append(result)
    return rows


class SuffixTree:
    def __init__(self, variables, second, width):
        self.dimension = 2 * width
        self.names = [name for name, _ in second]
        self.transitions = [transition for _, transition in second]
        missing = set(range(variables)) - set(self.names)
        identity = tuple(range(width))
        self.names.extend(sorted(missing))
        self.transitions.extend([(identity, identity)] * len(missing))
        assert len(self.names) == variables
        self.position = {name: i for i, name in enumerate(self.names)}
        self.factors = [(0, 0)] * variables
        self.size = 1
        while self.size < variables:
            self.size *= 2
        neutral = [{s: 1} for s in range(self.dimension)]
        self.nodes = [neutral for _ in range(2 * self.size)]
        for i in range(variables):
            self.nodes[self.size + i] = self.leaf(i)
        for i in range(self.size - 1, 0, -1):
            self.nodes[i] = compose(self.nodes[2 * i], self.nodes[2 * i + 1])

    def move(self, position, bit, state):
        toggled = self.factors[self.names[position]][bit]
        if toggled is None:
            return None
        current, parity = divmod(state, 2)
        return 2 * self.transitions[position][bit][current] + (parity ^ toggled)

    def leaf(self, position):
        rows = []
        for state in range(self.dimension):
            row = {}
            for bit in (0, 1):
                end = self.move(position, bit, state)
                if end is not None:
                    row[end] = (row.get(end, 0) + 1) % 3
            rows.append(row)
        return rows

    def update(self, name, effects):
        self.factors[name] = effects
        position = self.position[name]
        i = self.size + position
        self.nodes[i] = self.leaf(position)
        while i > 1:
            i //= 2
            self.nodes[i] = compose(self.nodes[2 * i], self.nodes[2 * i + 1])

    def witness(self, start, end):
        assignment = [0] * len(self.names)

        def visit(node, before, after):
            if node >= self.size:
                position = node - self.size
                if position < len(self.names):
                    assignment[self.names[position]] = next(
                        b for b in (0, 1) if self.move(position, b, before) == after)
                return
            left, right = self.nodes[2 * node], self.nodes[2 * node + 1]
            mid = next(m for m in left[before] if after in right[m])
            visit(2 * node, before, mid)
            visit(2 * node + 1, mid, after)

        visit(1, start, end)
        return tuple(assignment)


def last_reset(v, first, second, width, start1, accept1, start2, accept2):
    tree = SuffixTree(v, second, width)
    answer, count = None, 0

    def record(seed):
        nonlocal answer, count
        start = 2 * start2 + seed
        for end, residue in tree.nodes[1][start].items():
            state, parity = divmod(end, 2)
            if state in accept2 and parity in accept1:
                count = (count + residue) % 3
                if answer is None:
                    answer = tree.witness(start, end)

    for name, table in reversed(first):
        suffix = tree.factors[name]
        new = [None, None]
        for bit in (0, 1):
            if suffix[bit] is None:
                continue
            lo, hi = step(table, bit, 0), step(table, bit, 1)
            if lo == hi:
                pinned = [None, None]
                pinned[bit] = suffix[bit]
                tree.update(name, tuple(pinned))
                record(lo)
            else:
                new[bit] = suffix[bit] ^ lo
        tree.update(name, tuple(new))
    record(start1)
    return count, answer


def accepts(word, first, second, s1, a1, s2, a2):
    for name, table in first:
        s1 = step(table, word[name], s1)
    for name, transitions in second:
        s2 = transitions[word[name]][s2]
    return s1 in a1 and s2 in a2


def check(v, first, second, d, s1, a1, s2, a2):
    residue, witness = last_reset(v, first, second, d, s1, a1, s2, a2)
    count = sum(accepts(word, first, second, s1, a1, s2, a2)
                for word in product((0, 1), repeat=v))
    assert residue == count % 3 and (witness is not None) == bool(count)
    if witness is not None:
        assert accepts(witness, first, second, s1, a1, s2, a2)
    return count


def main():
    rng = Random(1957)
    zero_residue_positive = 0
    for _ in range(1200):
        v, d = rng.randrange(9), rng.randrange(1, 5)
        first = ([(rng.randrange(v), rng.randrange(16)) for _ in range(rng.randrange(22))]
                 if v else [])
        names = rng.sample(range(v), rng.randrange(v + 1))
        second = [(name, tuple(tuple(rng.randrange(d) for _ in range(d)) for _ in range(2)))
                  for name in names]
        a1 = {x for x in range(2) if rng.randrange(2)}
        a2 = {x for x in range(d) if rng.randrange(2)}
        count = check(v, first, second, d, rng.randrange(2), a1, rng.randrange(d), a2)
        zero_residue_positive += count > 0 and count % 3 == 0
    # Both values reset at the last row, and each value was also read before.
    for t, u in product(range(16), repeat=2):
        first = [(0, t), (1, u), (0, 12)]
        second = [(1, ((0, 1), (1, 0))), (0, ((0, 0), (0, 1)))]
        check(2, first, second, 2, 1, {1}, 0, {0})
    assert zero_residue_positive
    print(f"1,200 seeded cases and 256 two-name cases; {zero_residue_positive} "
          "seeded positive counts with zero residue. All decisions, residues and witnesses agree.")


if __name__ == "__main__":
    main()
