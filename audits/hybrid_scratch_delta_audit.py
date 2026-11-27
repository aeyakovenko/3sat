"""Replay chronological intervals independently using sorted scratch patches."""

from bisect import bisect_left
from collections import Counter, defaultdict
from itertools import product


class Overlay:
    def __init__(self, incoming):
        self.incoming = incoming
        self.written = {}
        self.touched = set()

    def load(self, address):
        self.touched.add(address)
        if address in self.written:
            return self.written[address]
        return self.incoming(address)

    def store(self, address, value):
        self.touched.add(address)
        self.written[address] = value


class ReferenceMemory:
    def __init__(self):
        self.words = {}

    def load(self, address):
        return self.words.get(address, 0)

    def store(self, address, value):
        if value:
            self.words[address] = value
        else:
            self.words.pop(address, None)


def execute(operations, register, memory):
    for kind, address, operand in operations:
        if kind == "set":
            memory.store(address, operand)
        elif kind == "copy":
            memory.store(address, memory.load(operand))
        elif kind == "indirect":
            # Previous contents affect both a read address and the stored value.
            register = memory.load(address + memory.load(operand))
            memory.store(address + register, register + 1)
        else:
            raise ValueError(kind)
    return register


def reference(intervals):
    memory = ReferenceMemory()
    registers = [0]
    patches = []
    for interval in intervals:
        old = memory.words.copy()
        registers.append(execute(interval, registers[-1], memory))
        updates = [(a, memory.load(a)) for a in old.keys() | memory.words.keys()
                   if old.get(a, 0) != memory.load(a)]
        patches.append(tuple(sorted(updates)))
    # The terminal contents are unobserved. Only the final controller is required.
    return registers, tuple(patches[:-1])


def accepts(intervals, registers, patches):
    if len(patches) + 1 != len(intervals) or len(registers) != len(intervals) + 1:
        return False
    if registers[0] != 0:
        return False

    ends_by_address = defaultdict(list)
    values_by_address = defaultdict(list)
    for index, patch in enumerate(patches):
        previous = -1
        for address, value in patch:
            if address <= previous or value < 0:
                return False
            previous = address
            ends_by_address[address].append(index)
            values_by_address[address].append(value)

    # Deliberately verify out of order. Index i's outgoing patch first applies
    # to the next interval: bisect_left excludes writes from i and later.
    for index in reversed(range(len(intervals))):
        def incoming(address):
            slot = bisect_left(ends_by_address.get(address, ()), index) - 1
            if slot < 0:
                return 0
            return values_by_address[address][slot]

        overlay = Overlay(incoming)
        if execute(intervals[index], registers[index], overlay) != registers[index + 1]:
            return False
        if index == len(patches):
            continue
        declared = dict(patches[index])
        # Canonical net patches omit writes that restore the incoming value.
        if any(incoming(a) == value for a, value in declared.items()):
            return False
        for address in overlay.touched | declared.keys():
            old = incoming(address)
            actual = overlay.written.get(address, old)
            if actual != declared.get(address, old):
                return False
    return True


def audit(intervals, counts):
    registers, patches = reference(intervals)
    assert accepts(intervals, registers, patches)
    counts["honest"] += 1
    for i, p in enumerate(patches):
        def reject(candidate, category):
            mutated = patches[:i] + (candidate,) + patches[i + 1:]
            assert not accepts(intervals, registers, mutated), (intervals, p, candidate)
            counts[category] += 1

        # Test a false update to an address outside the entire executed program,
        # as well as a redundant zero-valued declaration.
        for inserted in (0, 11):
            reject(p + ((2**60 + 13, inserted),), "extra")
        for j, (a, value) in enumerate(p):
            reject(p[:j] + p[j + 1:], "omitted")
            reject(p[:j] + ((a, value + 1),) + p[j + 1:], "wrong value")
            reject(p[:j] + ((a, value),) + p[j:], "duplicate")
            if value == 0:
                counts["erasures"] += 1


def main():
    a, b = 2**43 + 2, 2**51 + 3
    choices = [("set", a, 0), ("set", a, 1), ("set", b, 2),
               ("copy", a, b), ("copy", b, a), ("indirect", a, b)]
    counts = Counter()
    for operations in product(choices, repeat=3):
        for cut1, cut2 in ((1, 2), (1, 3), (2, 3)):
            # Include a terminal read so the final nonempty patch is challenged.
            ends = sorted({j for j in (0, cut1, cut2, 3)})
            pieces = [operations[l:r] for l, r in zip(ends, ends[1:])]
            pieces.append((("indirect", a, b),))
            audit(pieces, counts)

    # Test restoring an address inside an interval, preserving a cold bank
    # across many boundaries, and then erasing its previous nonzero value.
    cold = [("set", (j + 1) * 7919, j + 1) for j in range(48)]
    intervals = [cold, [("set", a, 9)], [("set", a, 20), ("set", a, 9)],
                 [("copy", b, a)], [("set", a, 0)], [("indirect", b, a)]]
    assert reference(intervals)[1][2] == ()
    audit(intervals, counts)
    assert all(counts[k] for k in
               ("honest", "extra", "omitted", "wrong value", "duplicate", "erasures"))
    print(", ".join(f"{count} {name}" for name, count in counts.items()))


if __name__ == "__main__":
    main()
