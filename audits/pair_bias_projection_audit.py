"""Check the physical DIMACS projection on a dense template with two input bits.

All four inputs are serialized in full. This audit checks the layout and
bit projection; it does not run a SAT solver or verify the circuit lower bound.
"""

from functools import lru_cache
from itertools import product


def source(a, b):
    # Four fixed rows keep every original name live, including both 10 and 11.
    cover = [(-x, x + 1, x + 2) for x in (1, 4, 7, 10)]
    return cover + [(-1, 2, 10 + a), (-3, 4, 10 + b), (5, 6, 10 + a)]


@lru_cache(maxsize=None)
def forbidden_words(bad):
    triples = [
        [row for row in product((0, 1), repeat=3) if sum(row) % 2 == value]
        for value in bad
    ]
    return tuple(
        tuple(word[share] for share in range(3) for word in words)
        for words in product(*triples)
    )


class Names:
    def __init__(self, copies, source_variables):
        self.copies = copies
        self.radix = 10
        while self.radix < 3 * copies:
            self.radix *= 10
        self.raw = {
            self.share(x, block, which)
            for x in range(1, source_variables + 1)
            for block in range(copies)
            for which in range(3)
        }
        self.next_state = 1

    def share(self, x, block, which):
        return self.radix * x + 3 * block + which

    def fresh(self):
        while self.next_state in self.raw:
            self.next_state += 1
        state = self.next_state
        self.next_state += 1
        return state


def encode(copies, a, b):
    clauses = source(a, b)
    names = Names(copies, 12)
    widths = [3 if sum(lit < 0 for lit in c) % 2 else 4 for c in clauses]
    state_count = copies * (3 + sum(3 * q * 4**q for q in widths))
    last_state = state_count + len(names.raw)
    assert max(names.raw) < last_state
    activation = [
        [last_state + 1 + 3 * block + which for which in range(3)]
        for block in range(copies)
    ]
    count = 0
    body = bytearray()

    def emit(x, y, z):
        nonlocal count
        assert len({abs(x), abs(y), abs(z)}) == 3
        body.extend(f"{x} {y} {z} 0\n".encode("ascii"))
        count += 1

    def cycle_states(size):
        states = [names.fresh() for _ in range(size)]
        return states + [-states[0]]

    global_raw = [activation[block][j] for j in range(3) for block in range(copies)]
    states = cycle_states(len(global_raw))
    for j, x in enumerate(global_raw):
        y, z = states[j : j + 2]
        for px, py in product((0, 1), repeat=2):
            # Exclude the unique wrong value of the next state for these bits.
            pz = 1 ^ px ^ py
            emit(-x if px else x, -y if py else y, -z if pz else z)

    for block in range(copies):
        for clause in clauses:
            groups = [
                tuple(names.share(abs(lit), block, which) for which in range(3))
                for lit in clause
            ]
            bad = tuple(int(lit < 0) for lit in clause)
            if sum(bad) % 2 == 0:
                groups.append(activation[block])
                bad += (1,)
            raw = [g[which] for which in range(3) for g in groups]
            for p in forbidden_words(bad):
                states = cycle_states(len(raw))
                for j, (x, value) in enumerate(zip(raw, p)):
                    lit = -x if value else x
                    y, z = states[j : j + 2]
                    emit(lit, -y, z)
                    emit(lit, y, -z)

    assert names.next_state - 1 == last_state  # All raw-ID holes now hold cycle states.
    maximum = last_state + 3 * copies
    assert count == 13068 * copies
    return f"p cnf {maximum} {count}\n".encode("ascii") + body


def check(copies):
    names = Names(copies, 12)
    width = len(str(names.radix)) - 1
    for x in range(1, 13):
        for r in range(3 * copies):
            assert str(names.share(x, *divmod(r, 3))) == str(x) + f"{r:0{width}d}"

    table = [encode(copies, a, b) for a, b in product((0, 1), repeat=2)]
    assert len({len(file) for file in table}) == 1
    header, *lines = table[0].splitlines()
    p, cnf, maximum, count = header.split()
    assert (p, cnf) == (b"p", b"cnf") and len(lines) == int(count)
    seen = set()
    for line in lines:
        x, y, z, zero = map(int, line.split())
        assert zero == 0
        seen.update((abs(x), abs(y), abs(z)))
    assert seen == set(range(1, int(maximum) + 1))

    # At a varying byte the four outputs must be an actual copy of a or b.
    # ASCII digits 0 and 1 differ in precisely their low bit.
    labels = {(48, 48, 49, 49): 0, (48, 49, 48, 49): 1}
    positions = [0, 0]
    for column in zip(*table):
        if column[1:] != (column[0],) * 3:
            positions[labels[column]] += 1
    # A name in one unguarded row occurs 2*3*4^3 times per block.
    # Input a also changes the name in a guarded row, with 4^4 patterns.
    assert positions == [copies * (384 + 1536), copies * 384]
    print(
        f"t={copies}, radix={names.radix}, {len(lines)} clauses, "
        f"{len(table[0])} bytes, projected bit copies {positions}"
    )


if __name__ == "__main__":
    for t in (1, 4, 17):
        check(t)
