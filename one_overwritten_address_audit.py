"""Verify the two marked-execution counterexamples on butterfly data and queries."""

from dataclasses import dataclass, field
from itertools import product
from random import Random

from last_physical_word_pointer_audit import OrbitIndex


@dataclass(frozen=True)
class Word:
    value: int
    marked: bool = False


@dataclass
class Suffix:
    memory: dict[int, int]
    numerical: int = 0
    marked_stores: int = 0
    written_addresses: set[int] = field(default_factory=set)
    written_payloads: set[int] = field(default_factory=set)
    old_loads: int = 0

    def store(self, address, payload):
        if address.marked or payload.marked:
            self.marked_stores += 1
        else:
            self.written_addresses.add(address.value)
            self.written_payloads.add(payload.value)
        self.memory[address.value] = payload.value

    def load(self, address):
        self.old_loads += 1
        return Word(self.memory.get(address.value, 0), marked=True)

    def compare(self, x, y):
        self.numerical += int(x.marked or y.marked)
        return x.value == y.value


def path(degree, depth, source, sink):
    """Public edge addresses, biased by two to reserve both Boolean words."""
    side = degree**depth
    edges = []
    place = 1
    for level in range(depth):
        digit = (sink//place) % degree
        edge = ((level*side + source)*degree + digit) + 2
        edges.append(edge)
        source += (digit - (source//place) % degree) * place
        place *= degree
    assert source == sink and len(set(edges)) == depth
    return edges


def one_address(presence, edges, tag):
    suffix = Suffix({0: 0, **dict(enumerate(presence, start=2))})
    r = Word(1)
    for addr in edges:
        suffix.store(Word(1), Word(addr))
        r = suffix.load(r)
        r = suffix.load(r)
    answer = suffix.compare(r, Word(tag))
    assert suffix.numerical == 1 and suffix.marked_stores == 0
    assert suffix.written_addresses == {1}
    assert suffix.written_payloads == set(edges)
    assert suffix.old_loads == 2*len(edges)
    return answer


def one_payload(presence, edges, tag):
    old = {0: 0, 1: 1}
    head = 1
    for addr, bit in enumerate(presence, start=2):
        if not bit:
            old[addr], head = head, addr
    suffix = Suffix(old)
    for addr in edges:
        suffix.store(Word(addr), Word(0))
    r = Word(head)
    for _ in range(len(presence)+1):
        r = suffix.load(r)
    answer = suffix.compare(r, Word(tag))
    assert suffix.numerical == 1 and suffix.marked_stores == 0
    assert suffix.written_addresses == set(edges)
    assert suffix.written_payloads == {0}
    assert suffix.old_loads == len(presence)+1
    return answer


def graphs(number, rng):
    if number <= 10:
        yield from product(range(2), repeat=number)
        return
    yield (0,)*number
    yield (1,)*number
    # Includes both extreme graphs and every single-edge change from each.
    for bit, index in product(range(2), range(number)):
        data = [bit]*number
        data[index] = 1-bit
        yield data
    for _ in range(128):
        yield [rng.randrange(2) for _ in range(number)]


@dataclass(frozen=True)
class Deferred:
    origin: int
    versions: tuple


class CachedReplay:
    def __init__(self, memory):
        self.index = OrbitIndex(memory)
        self.cache = {}
        self.writes = []
        self.powers = 0
        self.label(0)

    def label(self, number):
        if number not in self.cache:
            self.cache[number] = self.index.labels.get(number)
        return self.cache[number]

    def hits(self, origin, steps, target):
        # No access to the old index in the equality test.
        if not steps:
            return origin == target
        u, v = self.cache[origin], self.cache[target]
        if u is None:
            return self.hits(0, steps-1, target)
        if v is None or u.cycle != v.cycle:
            return False
        if steps < u.depth:
            return v.depth == u.depth-steps and v.first <= u.first < v.end
        return v.depth == 0 and (u.entry+steps-u.depth) % u.period == v.entry

    def load(self, x):
        if isinstance(x, Deferred):
            return Deferred(x.origin, x.versions+(len(self.writes),))
        return Deferred(x, (len(self.writes),))

    def resolve(self, x):
        if not isinstance(x, Deferred):
            return x
        origin, steps = x.origin, 0
        self.label(origin)
        for version in x.versions:
            for key, value in reversed(self.writes[:version]):
                if self.hits(origin, steps, key):
                    origin, steps = value, 0
                    break
            else:
                steps += 1
        self.powers += 1
        return self.index.advance(origin, steps)

    def record(self, x, y):
        key, value = self.resolve(x), self.resolve(y)
        self.label(key)
        self.label(value)
        self.writes.append((key, value))
        return key, value


def audit_cached_replay(rng):
    length = 75
    total = 0
    for _ in range(1000):
        old = {j: rng.randrange(30) for j in rng.sample(range(44), 17)}
        direct = Suffix(dict(old))
        sim = CachedReplay(old)
        regs = [Word(i) for i in range(8)]
        virtual = list(range(8))
        for k in range(length):
            i, j, dst = (rng.randrange(8) for _ in range(3))
            u, v = regs[i], regs[j]
            x, y = virtual[i], virtual[j]
            move = rng.randrange(12)
            if move < 4:
                regs[dst], virtual[dst] = direct.load(u), sim.load(x)
            elif move < 7:
                # Unmarked updates from repeated, often overlapping alphabets.
                addr = rng.choice((0, 1, 2, 3, 5, 6, 9))
                val = rng.choice((0, 1, 2, 3, 5, 6, 7, 8, 21))
                direct.store(Word(addr), Word(val))
                sim.record(addr, val)
            elif move < 9:
                direct.store(u, v)
                assert sim.record(x, y) == (u.value, v.value)
            elif move == 9:
                assert direct.compare(u, v) == (sim.resolve(x) == sim.resolve(y))
            elif move == 10:
                direct.numerical += int(u.marked or v.marked)
                regs[dst] = Word(u.value ^ v.value)
                virtual[dst] = sim.resolve(x) ^ sim.resolve(y)
                assert regs[dst].value == virtual[dst]
            else:
                regs[dst], virtual[dst] = u, x
            endpoints = direct.written_addresses | direct.written_payloads
            # One initial label. At most two label/power accesses per marked
            # operand and two additional endpoint labels per marked STORE.
            assert len(sim.cache)+sim.powers <= (1 + len(endpoints)
                       + 4*direct.numerical + 6*direct.marked_stores)
            total += 1
    print(f"{total:,} step prefixes verified with the cached-label charge.")


def audit():
    rng = Random(2759)
    audit_cached_replay(rng)
    checks = 0
    for degree, depth in ((2, 1), (2, 2), (2, 3), (4, 2)):
        side = degree**depth
        n_edges = side*degree*depth
        for present in graphs(n_edges, rng):
            for source, sink in product(range(side), repeat=2):
                edges = path(degree, depth, source, sink)
                reachable = all(present[k-2] for k in edges)
                for tag in (0, 1):
                    expected = reachable == bool(tag)
                    assert one_address(present, edges, tag) == expected
                    assert one_payload(present, edges, tag) == expected
                    checks += 1
    print(f"{checks:,} signed butterfly queries checked with both marked-instruction programs.")


if __name__ == '__main__':
    audit()
