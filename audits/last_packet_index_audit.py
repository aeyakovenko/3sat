"""Exhaust compact decimal-mask data records and a last query word for k indexing.

Each query selects one bit from each bank and asks whether their AND equals
its last tag. Requires pycosat; small examples use aligned 64-byte words.
"""

from itertools import product

import pycosat

from last_butterfly_word_audit import LazyRecords, QueryNeeded, WORD_BYTES, line, pad, read_packets
from table_probe_context_audit import parse


class IndexedAnd:
    def __init__(self, m, k):
        assert m in (2, 4) and k in (2, 3)
        self.m, self.k = m, k
        self.tags = {(j, bits): int(f"{j+1}{bits[0]}{bits[1]}")
                     for j in range(k) for bits in product((0, 1), repeat=2)}
        # The final tag changes one 2/3 ASCII digit of its positive unit.
        mode0 = 10*(1+max(self.tags.values())//10)+2
        self.mode = (mode0, mode0+1)
        self.last = mode0+1
        reserved = set(self.tags.values()) | set(self.mode) | {1,2,3,4}
        self.rows = [tuple(-i if (v >> (i-1)) & 1 else i for i in (1,2,3))
                     for v in range(1, 8)]
        self.add(4)
        for v in range(5, self.last+1):
            if v not in reserved:
                self.add(-v)
        self.add(*self.mode)
        self.add(-self.mode[0], -self.mode[1])
        self.indices = []
        self.values = []
        self.high = []
        for j in range(k):
            leaves = [self.fresh() for _ in range(m)]
            self.indices.append(leaves)
            seen = leaves[0]
            for leaf in leaves[1:]:
                self.add(-seen, -leaf)
                seen = self.combine(seen, leaf, True)
            self.add(seen)
            highs = [self.any(leaves[start:start+2]) for start in range(0, m, 2)]
            self.high.append(highs)
            lows = [self.any(leaves[o::2]) for o in range(2)]
            value = self.fresh()
            self.values.append(value)
            for bits in product((0,1), repeat=2):
                name = self.tags[j,bits]
                for low, bit in zip(lows, bits):
                    equal = value if bit else -value
                    self.add(-low, -equal, name)
                    self.add(-low, equal, -name)
        result = self.values[0]
        for v in self.values[1:]:
            result = self.combine(result, v, False)
        self.add(-result, self.mode[1])
        self.add(result, -self.mode[1])
        self.num_records = k*(m//2)+1
        count = len(self.rows) + self.num_records*(k+1)
        head = f"p cnf {self.last} {count}\n".encode() + b"".join(map(line, self.rows))
        self.prefix = pad(head, WORD_BYTES*((len(head)+WORD_BYTES-1)//WORD_BYTES))

    def fresh(self):
        self.last += 1
        return self.last

    def add(self, *args):
        row = list(args)
        for anchor in (1,2,3):
            if len(row) < 3 and anchor not in map(abs, row):
                row.append(anchor)
        assert len(set(map(abs, row))) == len(row) == 3
        self.rows.append(tuple(row))

    def combine(self, x, y, is_or):
        z = self.fresh()
        if is_or:
            self.add(-x, z)
            self.add(-y, z)
            self.add(x, y, -z)
        else:
            self.add(x, -z)
            self.add(y, -z)
            self.add(-x, -y, z)
        return z

    def any(self, bits):
        result = bits[0]
        for b in bits[1:]:
            result = self.combine(result, b, True)
        return result

    def packets(self, db):
        words = []
        for j in range(self.k):
            for g, active in enumerate(self.high[j]):
                bits = tuple((db >> (self.m*j+2*g+i)) & 1 for i in range(2))
                guarded = line((-active, self.tags[j,bits], 1))
                # Padding is fixed and contains the forced true name 4.
                raw = b"c D\n" + guarded + line((4, 1, 2))*self.k
                words.append(pad(raw, WORD_BYTES))
        return tuple(words)

    def query(self, indices, b):
        units = [self.indices[j][i] for j, i in enumerate(indices)] + [self.mode[b]]
        return pad(b"c Q\n"+b"".join(line((v,1,2)) for v in units), WORD_BYTES)

    def check_model(self, layout, db, indices, b):
        source = self.prefix + b"".join(layout)
        assert len(self.prefix) % WORD_BYTES == 0 and all(len(w) == WORD_BYTES for w in layout)
        body = b"\n".join(l for l in source.splitlines() if l.strip() and not l.startswith(b"c "))
        clauses, variables = parse(body+b"\n")
        models = pycosat.itersolve(clauses, vars=variables)
        first = next(models, None)
        assert next(models, None) is None
        selected = [(db >> (j*self.m+i)) & 1 for j, i in enumerate(indices)]
        expected = int(all(selected)) == b
        assert (first is not None) == expected
        if expected:
            truth = {v for v in first if v > 0}
            for j, i in enumerate(indices):
                assert [t for t, v in enumerate(self.indices[j]) if v in truth] == [i]
                assert int(self.values[j] in truth) == selected[j]
            for (j, bits), name in self.tags.items():
                assert (name in truth) == (selected[j] == bits[indices[j] % 2])
            assert self.mode[b] in truth and self.mode[1-b] not in truth
        return expected


def check(m, k):
    layout = IndexedAnd(m, k)
    dbs = [layout.packets(db) for db in range(1 << (m*k))]
    wire_edges = 0
    for db, words in enumerate(dbs):
        raw = b"".join(words)
        for bit in range(m*k):
            if not (db & (1 << bit)):
                changed = b"".join(dbs[db | (1 << bit)])
                assert [(a,b) for a,b in zip(raw,changed) if a != b] == [(48,49)]
                wire_edges += 1
    files = models = twins = 0
    holes = set()
    for db, words in enumerate(dbs):
        lazy = LazyRecords(words)
        prefix = []
        try:
            read_packets(layout.num_records, "adaptive", lazy.load, prefix)
        except QueryNeeded:
            pass
        assert lazy.final is not None and len(lazy.placed) == len(words)
        holes.add(lazy.final)
        for indices in product(range(m), repeat=k):
            pair = [layout.query(indices, b) for b in (0,1)]
            assert [(x,y) for x,y in zip(*pair) if x != y] == [(50,51)]
            sat = []
            for b, query in enumerate(pair):
                actual = lazy.complete(query)
                trace = []
                read_packets(layout.num_records, "adaptive", actual.__getitem__, trace)
                assert trace == prefix + [(lazy.final, query)]
                sat.append(layout.check_model(actual, db, indices, b))
            assert sat[0] != sat[1]
            files += 2
            models += sum(sat)
            twins += 1
    print(f"m={m}, k={k}: {len(dbs)} complete databases, {m**k} index tuples, "
          f"{files} files, {models} unique models, {twins} opposite one-bit last-word pairs")
    print(f"  {wire_edges} physical one-bit database edges in fixed packet order; "
          f"{len(holes)} adaptive final addresses; {layout.num_records} variable packet slots")


if __name__ == "__main__":
    check(2, 3)
    check(4, 2)
