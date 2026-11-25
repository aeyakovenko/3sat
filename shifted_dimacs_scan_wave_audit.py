"""Verify the wave in the compulsory scan M[M[p]] = (p+1) mod Q.

A run-length map simulates every address of an ascending pass, even when the
valid DIMACS instance has more words than can be materialized. The bulk step
stops at the next input change or before its own write would change a future
read. Small whole arrays independently check this implementation.
"""

from bisect import bisect_left, bisect_right
from itertools import product


class Memory:
    def __init__(self, size, runs):
        self.size = size
        self.start = [p for p, _ in runs]
        self.val = dict(runs)
        assert self.start[0] == 0

    def interval(self, p):
        i = bisect_right(self.start, p)
        return self.val[self.start[i - 1]], self.start[i] if i < len(self.start) else self.size

    def set_boundary(self, p, value):
        if p not in self.val:
            self.start.insert(bisect_left(self.start, p), p)
        self.val[p] = value

    def remove_redundant(self, p):
        if not p or p not in self.val:
            return
        i = bisect_left(self.start, p)
        if self.val[self.start[i - 1]] == self.val[p]:
            self.start.pop(i)
            del self.val[p]

    def write(self, p, value):
        old, stop = self.interval(p)
        if old == value:
            return
        if p + 1 < stop:
            self.set_boundary(p + 1, old)
        self.set_boundary(p, value)
        self.remove_redundant(p)
        self.remove_redundant(p + 1)

    def pass_once(self):
        p = 0
        while p < self.size:
            destination, stop = self.interval(p)
            if p <= destination < stop:
                stop = destination if p < destination else p + 1
            # All these steps read the same destination. Only the final
            # payload survives, since none of their later reads sees the write.
            self.write(destination, stop % self.size)
            p = stop

    def cells(self):
        out = []
        for start, stop, value in self.runs():
            out.extend([value] * (stop - start))
        return out

    def runs(self):
        for start, stop in zip(self.start, self.start[1:] + [self.size]):
            yield start, stop, self.val[start]


def full_pass(memory):
    size = len(memory)
    for p in range(size):
        memory[memory[p]] = (p + 1) % size


def check_run_length_engine():
    cases = 0
    for q in range(1, 5):
        for raw in product(range(q), repeat=q):
            runs = [(i, v) for i, v in enumerate(raw) if i == 0 or v != raw[i - 1]]
            compact = Memory(q, runs)
            full = list(raw)
            for _ in range(8):
                compact.pass_once()
                full_pass(full)
                assert compact.cells() == full
            cases += 1
    return cases


def check_frontier(memory, m, first, spaces, t):
    a = m + t - 1
    h = spaces + t
    bounds = ((0, a), (first, first + t), (spaces, h))
    assert a < first and first + t < spaces and h < memory.size - 1
    locations = {a: [], h: []}
    for start, stop, val in memory.runs():
        if val:
            assert any(lo <= start < stop <= hi + 1 for lo, hi in bounds)
            assert any(lo <= val <= hi for lo, hi in bounds)
        if val in locations:
            locations[val].append((start, stop))
    assert locations[a] == [(h - 1, h)]
    assert locations[h] == [(a, a + 1)]


def wave(q, m, first, spaces, passes, crosscheck):
    runs = [(0, first), (1, spaces), (m, 0)]
    mem = Memory(q, runs)
    full = mem.cells() if crosscheck else None
    for t in range(1, passes + 1):
        mem.pass_once()
        if full is not None:
            full_pass(full)
            assert mem.cells() == full
        check_frontier(mem, m, first, spaces, t)


def check_dimacs(width):
    size = 1 << width
    word_bytes = width // 8
    first_word = b"p cnf 3 1\n1 2 3 0".ljust(word_bytes - 1, b" ") + b"\n"
    spaces_word = b" " * word_bytes
    assert len(first_word) == word_bytes and first_word.split() == b"p cnf 3 1 1 2 3 0".split()
    assert (first_word + 17 * spaces_word).split() == first_word.split()
    first = int.from_bytes(first_word, "little")
    spaces = int.from_bytes(spaces_word, "little")
    m = size // (2 * width)
    n = m * width
    assert 16 * (((n + 1).bit_length() + 15) // 16) == width
    assert m + size // 512 < first and first + size // 512 < spaces < size - size // 512 - 1
    # This is the complete machine state arising from exactly m DIMACS words.
    wave(size, m, first, spaces, 65, crosscheck=False)


if __name__ == "__main__":
    print(check_run_length_engine(), "complete small initial states, eight passes each")
    wave(65536, 2048, 0x0a30, 0x2020, 128, crosscheck=True)
    print("128 complete passes at Q=65536 checked against full memory (arithmetic analogue)")
    for word_bits in (160, 192, 256, 512):
        check_dimacs(word_bits)
    print("65 complete passes each on four proper width-consistent implicit DIMACS files")
