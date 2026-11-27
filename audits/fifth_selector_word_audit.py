"""Execute the 21-bit selector programs and audit each of the five tight encodings."""

from collections import Counter

import numpy as np


def labels(length, codes):
    k = length // 2
    mask = (1 << k) - 1
    positive = codes & mask
    negative = (codes >> k) & mask
    free = ((codes >> (2 * k)) == 0) if length % 2 else False
    return ((positive & negative) == 0) & ((negative != mask) | free)


def embed(length, codes):
    if length % 2 == 0:
        return codes | (1 << length)
    # Insert a zero positive-unit selector before the negative sign plane.
    k = length // 2
    lower = (1 << k) - 1
    return (codes & lower) | ((codes & ~lower) << 1)


def adjacent():
    for length in range(16, 21):
        parent = np.arange(1 << length)
        child = embed(length, parent)
        assert len(np.unique(child)) == len(parent)
        assert np.array_equal(labels(length, parent), labels(length + 1, child))
        new_bit = length if length % 2 == 0 else length // 2
        changes = np.count_nonzero(labels(length + 1, child ^ (1 << new_bit)) != labels(length, parent))
        assert changes
        print(f"{length} to {length+1}: all {len(parent)} old files preserved, "
              f"{changes} fibers change verdict when the new bit is toggled.")


# A target -1 accepts and -2 rejects. All other entries are instruction labels.
# Words can be read by a literal address or using register 4 as the address.
PREFIX = [
    ("load", 0, 3),             # 0. r0 = N
    ("eq-lit", 0, 31, 2, 12),   # 1
    ("load", 1, 1),             # 2. r1 = Q
    ("eq-lit", 1, 0, 4, -2),    # 3
    ("load", 2, 2),             # 4. r2 = M
    ("eq-lit", 2, 31, 6, 9),    # 5
]
SUFFIX = [
    ("load", 3, 0),             # 9. r3 = P
    ("and", 5, 2, 3),           # 10
    ("eq-lit", 5, 0, -1, -2),   # 11
    ("load", 1, 1),             # 12. r1 = Q
    ("and", 5, 0, 1),           # 13
    ("eq-lit", 5, 0, 15, -2),   # 14
    ("load", 3, 0),             # 15. r3 = P
    ("load", 2, 2),             # 16. r2 = M
    ("and", 5, 2, 3),           # 17
    ("eq-lit", 5, 0, -1, -2),   # 18
]
TAIL = {
    "negative-unit": [("load", 4, 4), ("indirect", 5, 4), ("eq", 5, 4, -1, -2)],
    "enable-disjunct": [("load", 3, 0), ("load", 4, 4), ("ult", 3, 4, -1, -2)],
}


def execute(program, files):
    words = np.stack([(files >> (5 * i)) & 31 for i in range(5)])
    pc = np.zeros(len(files), dtype=np.int8)
    steps = np.zeros_like(pc)
    regs = np.zeros((6, len(files)), dtype=np.uint8)
    while (pc >= 0).any():
        before = pc.copy()
        steps[before >= 0] += 1
        for label in np.unique(before[before >= 0]):
            ix = np.flatnonzero(before == label)
            op, a, b, *rest = program[label]
            if op == "load":
                regs[a, ix] = words[b, ix]
            elif op == "indirect":
                addr = regs[b, ix]
                regs[a, ix] = 0
                original = addr < 5
                regs[a, ix[original]] = words[addr[original], ix[original]]
            elif op == "and":
                regs[a, ix] = regs[b, ix] & regs[rest[0], ix]
            else:
                if op == "eq-lit":
                    guard = regs[a, ix] == b
                elif op == "eq":
                    guard = regs[a, ix] == regs[b, ix]
                else:
                    assert op == "ult"
                    guard = regs[a, ix] < regs[b, ix]
                pc[ix] = np.where(guard, *rest)
                continue
            pc[ix] = label + 1
        assert steps.max() <= 9
    return pc == -1, steps


def fifth_word():
    for kind, tail in TAIL.items():
        clocks = Counter()
        accepted = 0
        for start in range(0, 1 << 21, 1 << 15):
            files = np.arange(start, start + (1 << 15))
            verdict, steps = execute(PREFIX + tail + SUFFIX, files)
            expected = labels(21, files if kind == "negative-unit" else files ^ (1 << 20))
            assert np.array_equal(verdict, expected)
            accepted += int(verdict.sum())
            times, counts = np.unique(steps, return_counts=True)
            clocks.update({int(t): int(v) for t, v in zip(times, counts)})
        assert accepted == 2 * 3**10 - 1 and sum(clocks.values()) == 1 << 21
        print(f"{kind}: all {1<<21} files checked, {accepted} SAT, clocks {dict(sorted(clocks.items()))}.")


if __name__ == "__main__":
    adjacent()
    fifth_word()
