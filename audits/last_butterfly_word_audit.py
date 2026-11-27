"""Real proper DIMACS packets for the adaptive last-word butterfly reduction.

Requires pycosat. The native input interface tested here reads aligned words.
"""

from functools import lru_cache
from itertools import product
from random import Random

from table_probe_context_audit import parse


WORD_BYTES = 64
ORDERS = ("forward", "reverse", "adaptive")


def line(clause):
    return (" ".join(map(str, clause)) + " 0\n").encode()


def pad(raw, length):
    space = length - len(raw)
    assert space >= 0 and raw.endswith(b"\n")
    return raw + (b" " * (space-1) + b"\n" if space else b"")


def packet(tag, first, second):
    return pad(b"c " + tag + b"\n" + line(first) + line(second), WORD_BYTES)


class Butterfly:
    def __init__(self, depth, signed=False):
        self.depth = depth
        self.side = 1 << depth
        self.endpoints = []
        self.data = []
        for level, u, digit in product(range(depth), range(self.side), range(2)):
            v = (u & ~(1 << level)) | (digit << level)
            left, right = self.name(level, u), self.name(level+1, v)
            self.endpoints.append((left, right))
            if signed:
                # A missing edge switches the state to 1. State 1 persists.
                self.data.append(tuple(packet(b"M",
                    (-self.state(left, 0), self.state(right, 1-present), 1),
                    (-self.state(left, 1), self.state(right, 1), 1)) for present in (0, 1)))
            else:
                disabled, enabled = (-left, right, 4), (-left, right, 1)
                self.data.append((packet(b"D", disabled, disabled), packet(b"D", enabled, enabled)))
        self.records = len(self.data) + 1
        self.queries = {}
        for s, t in product(range(self.side), repeat=2):
            source, sink = self.name(0, s), self.name(depth, t)
            for b in ((0,1) if signed else (0,)):
                u = self.state(source, 0) if signed else source
                v = self.state(sink, b) if signed else sink
                self.queries[s,t,b] = packet(b"Q", (u, 1, 2), (-v, 1, 2))
        fixed = [tuple(-i if (v >> (i-1)) & 1 else i for i in (1, 2, 3))
                 for v in range(1, 8)]
        fixed.append((4, 1, 2))
        names = self.name(depth, self.side-1)
        if signed:
            used = {self.state(v, b) for v in range(5, names+1) for b in (0, 1)}
            names = max(used)
            fixed.extend((-v,1,2) for v in range(5, names+1) if v not in used)
            fixed.extend((v,4,1) for v in sorted(used))
        header = f"p cnf {names} {len(fixed)+2*self.records}\n".encode()
        raw = header + b"".join(line(row) for row in fixed)
        self.prefix = pad(raw, WORD_BYTES*((len(raw)+WORD_BYTES-1)//WORD_BYTES))

    def name(self, level, index):
        return 5 + self.side*level + index

    @staticmethod
    def state(vertex, flag):
        return 10*vertex+2+flag

    def reaches(self, mask, source, sink):
        vertex = source
        for level in range(self.depth):
            digit = (sink >> level) & 1
            edge = 2*(level*self.side+vertex)+digit
            if not (mask & (1 << edge)):
                return False
            vertex = (vertex & ~(1 << level)) | (digit << level)
        assert vertex == sink
        return True


class QueryNeeded(Exception):
    pass


class LazyRecords:
    def __init__(self, records):
        self.data = records
        self.placed = {}
        self.final = None

    def load(self, position):
        if position in self.placed:
            return self.placed[position]
        count = len(self.placed)
        if count == len(self.data):
            self.final = position
            raise QueryNeeded
        self.placed[position] = self.data[count]
        return self.placed[position]

    def complete(self, query):
        assert self.final is not None and self.final not in self.placed
        return tuple(query if i == self.final else self.placed[i]
                     for i in range(len(self.data)+1))


def read_packets(number, order, load, trace):
    """A deterministic adaptive order with deliberate reads of known addresses."""
    unseen = list(range(number))
    seen = []
    state = 3

    def read(i):
        raw = load(i)
        trace.append((i, raw))
        return raw

    while unseen:
        if order == "forward":
            pos = 0
        elif order == "reverse":
            pos = -1
        else:
            pos = state % len(unseen)
        key = unseen.pop(pos)
        raw = read(key)
        seen.append(key)
        if unseen and not (len(seen) % 2):
            again = seen[state % len(seen)]
            assert read(again) == next(value for index, value in trace if index == again)
        state = (state*37 + sum(raw) + key) & 65535


@lru_cache(maxsize=None)
def decode(raw):
    rows = [tuple(map(int, l.split())) for l in raw.splitlines()
            if l.strip() and not l.startswith(b"c ")]
    assert len(rows) == 2 and all(len(r) == 4 and r[-1] == 0 for r in rows)
    if raw.startswith(b"c D\n"):
        assert rows[0] == rows[1]
        a, b, flag, _ = rows[0]
        assert a < -4 and b > 4 and flag in (1, 4)
        return (((-a, b),) if flag == 1 else ()), None
    if raw.startswith(b"c M\n"):
        assert all(r[0] < -4 and r[1] > 4 and r[2] == 1 for r in rows)
        return tuple((-r[0], r[1]) for r in rows), None
    assert raw.startswith(b"c Q\n") and rows[0][1:] == rows[1][1:] == (1, 2, 0)
    return (), (rows[0][0], -rows[1][0])


def packet_verdict(records):
    adjacency = {}
    query = None
    for raw in records:
        edges, endpoints = decode(raw)
        if endpoints is not None:
            assert query is None
            query = endpoints
        for u, v in edges:
            adjacency.setdefault(u, []).append(v)
    source, sink = query
    queue = [source]
    reached = {source}
    for u in queue:
        for v in adjacency.get(u, ()):
            if v not in reached:
                reached.add(v)
                queue.append(v)
    return sink not in reached


def physical_verdict(graph, records):
    import pycosat

    data = graph.prefix + b"".join(records)
    for i, raw in enumerate(records):
        begin = len(graph.prefix) + i*WORD_BYTES
        assert begin % WORD_BYTES == 0 and data[begin:begin+WORD_BYTES] == raw
    body = b"\n".join(l for l in data.splitlines() if l.strip() and not l.startswith(b"c "))
    clauses, variables = parse(body + b"\n")
    return pycosat.solve(clauses, vars=variables) != "UNSAT"


def check(depth, masks, signed=False):
    graph = Butterfly(depth, signed)
    files = rejections = repeated = signed_pairs = 0
    adaptive_final_addresses = set()
    for mask in masks:
        data = tuple(pair[(mask >> i) & 1] for i, pair in enumerate(graph.data))
        for order in ORDERS:
            lazy = LazyRecords(data)
            common = []
            try:
                read_packets(graph.records, order, lazy.load, common)
            except QueryNeeded:
                pass
            assert lazy.final is not None and len(lazy.placed) == len(data)
            assert len({i for i, _ in common}) == len(data)
            assert all(i != lazy.final for i, _ in common)
            repeated += len(common)-len(data)
            if order == "adaptive":
                adaptive_final_addresses.add(lazy.final)
            outcomes = {}
            for (source, sink, b), query in graph.queries.items():
                layout = lazy.complete(query)
                transcript = []
                read_packets(graph.records, order, layout.__getitem__, transcript)
                assert transcript == common + [(lazy.final, query)]
                assert set(layout) == set(data) | {query}
                reached = graph.reaches(mask, source, sink)
                expected = (bool(b) == reached) if signed else not reached
                received = dict(transcript)
                cached = [received[i] for i in range(len(layout))]
                assert packet_verdict(cached) == physical_verdict(graph, layout) == expected
                outcomes[source,sink,b] = expected
                files += 1
                rejections += not expected
            if signed:
                for s, t in product(range(graph.side), repeat=2):
                    left, right = (graph.queries[s,t,b] for b in (0, 1))
                    changes = [(x,y) for x,y in zip(left,right) if x != y]
                    assert changes == [(ord("2"), ord("3"))]
                    assert outcomes[s,t,0] != outcomes[s,t,1]
                    signed_pairs += 1
    assert len(adaptive_final_addresses) > 1 and repeated
    print(f"depth {depth}, signed={signed}: {len(masks)} subgraphs, {len(graph.queries)} queries each, "
          f"{len(ORDERS)} orders; {files} files, {rejections} UNSAT")
    print(f"  {len(adaptive_final_addresses)} distinct last addresses in the data-dependent order; "
          f"{repeated} genuine repeated prefix loads before query completion")
    if signed:
        print(f"  {signed_pairs} opposite-verdict one-ASCII-bit last-packet pairs")


if __name__ == "__main__":
    check(1, range(16))  # every subgraph and every source/sink pair
    rng = Random(20315)
    masks = {0, 65535, *(65535 ^ (1 << i) for i in range(16))}
    masks.update(rng.randrange(65536) for _ in range(32))
    check(2, sorted(masks))
    check(1, range(16), signed=True)
    check(2, sorted(masks), signed=True)
