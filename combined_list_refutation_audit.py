"""Audit the disjunction layout on a seven-vertex cycle, without testing degree."""
from itertools import combinations, product
from random import Random

from dense_ascii_chunk_circuit_audit import encode, sat_from_bytes


def parsed_list(k, values):
    header, *lines = encode(k, values).decode("ascii").splitlines()
    return int(header.split()[2]), [tuple(map(int, line.split()[:3])) for line in lines]


class Builder:
    def __init__(self, start):
        self.maximum = start

    def fresh(self):
        self.maximum += 1
        return self.maximum

    def proper(self, clauses):
        false_bits = [self.fresh() for _ in range(3)]
        rows = [tuple(-v if b else v for v, b in zip(false_bits, bits))
                for bits in product((0, 1), repeat=3) if any(bits)]
        for clause in clauses:
            rows.append(tuple(clause) + tuple(false_bits[:3-len(clause)]))
        return rows

    def gated(self, gate, clauses):
        rows = []
        for a, b, c in clauses:
            h = self.fresh()
            rows.extend(((gate, a, h), (-h, b, c)))
        return rows


def field_branches(b, n):
    # Seven charges of one cannot be the boundary of a flow modulo 2 or 3.
    edge = [b.fresh() for _ in range(n)]
    two = []
    for v in range(n):
        a, d = edge[v-1], edge[v]
        two.extend(((a, d), (-a, -d)))
    three = []
    directed = {}
    for u in range(n):
        for v in ((u-1) % n, (u+1) % n):
            slots = [b.fresh() for _ in range(3)]
            directed[u, v] = slots
            three.append(tuple(slots))
            three.extend((-i, -j) for i, j in combinations(slots, 2))
    for u in range(n):
        v = (u+1) % n
        prev = (u-1) % n
        for i, j in product(range(3), repeat=2):
            if (i+j) % 3:
                three.append((-directed[u, v][i], -directed[v, u][j]))
            if (i+j) % 3 != 1:
                three.append((-directed[u, v][i], -directed[u, prev][j]))
    s = b.fresh()
    return b.gated(s, b.proper(two)) + b.gated(-s, b.proper(three))


def serialized(k, values):
    maximum, list_rows = parsed_list(k, values)
    builder = Builder(maximum)
    hard = field_branches(builder, 7)
    selector = builder.fresh()
    rows = builder.gated(selector, list_rows) + builder.gated(-selector, hard)
    header = f"p cnf {builder.maximum} {len(rows)}\n"
    body = "".join(f"{a} {b} {c} 0\n" for a, b, c in rows)
    return (f"c {k} 7 6 1 0 2 1 3 2 4 3 5 4 6 5 0\n" + header + body).encode("ascii")


def main():
    rng = Random(1618)
    tested = columns = 0
    for k in (1, 2, 3):
        m, b = 2**k, 2*k
        baseline = serialized(k, [0]*m)
        changed = set()
        for i, j in product(range(m), range(b)):
            values = [0]*m
            values[i] = 1 << j
            output = serialized(k, values)
            assert len(output) == len(baseline)
            delta = {offset for offset, (x, y) in enumerate(zip(baseline, output)) if x != y}
            assert len(delta) == 2 and delta.isdisjoint(changed)
            assert all((baseline[t], output[t]) == (48, 49) for t in delta)
            changed.update(delta)
            columns += 1
        samples = [list(range(m)), [0]*m]
        for _ in range(8):
            samples.append([rng.randrange(1 << b) for _ in range(m)])
        for values in samples:
            file = serialized(k, values)
            assert sat_from_bytes(file.split(b"\n", 1)[1]) == (len(set(values)) != m)
            tested += 1
    print(f"{tested} combined DIMACS files and {columns} physical bit columns passed")


if __name__ == "__main__":
    main()
