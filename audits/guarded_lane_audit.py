"""Two controls, a nonconstant SAT payload, and actual guarded single-lane orders.

Run from the 3sat research repository. No optional solver or nonstandard dependency.
"""

from dataclasses import replace
from itertools import pairwise, permutations, product

from one_point_strip_audit import anchor_audit
from single_lane_sat import TIPS, compile_lane, extend_coloring, site
from two_hamilton_paths_sat_audit import encode

FALSE, TRUE, BASE = 0, 1, 2
PALETTE = tuple(permutations(range(3)))


def guarded_clauses(payload):
    # Each control carries a parity flag and three flags for its value mod 3.
    # Variable 9 must be the XOR of the two parity flags 1 and 5.
    clauses = []
    for u, v in product(range(2), repeat=2):
        clauses.append((1 if not u else -1, 5 if not v else -5, 9 if u ^ v else -9))
    for i, j in product(range(3), repeat=2):
        labels = (-(2 + i), -(6 + j))
        r = (i + j) % 3
        if r == 2:
            clauses.append(labels)
        else:
            clauses.append(labels + ((9,) if r == 1 else (-9,)))
            if r == 0:
                clauses.extend(labels + (literal,) for literal in payload)
    return tuple(clauses)


def payload_bits(b, assignment):
    row = {}
    for i, a in enumerate(b):
        row[4 * i + 1] = a % 2
        for j in range(3):
            row[4 * i + 2 + j] = int(a % 3 == j)
    row[9] = row[1] ^ row[5]
    row[10], row[11] = assignment
    return row


def literal(bits, lit):
    return bits[abs(lit)] ^ (lit < 0)


class PaletteGraph:
    def __init__(self, clauses):
        self.edges = [(FALSE, TRUE), (FALSE, BASE), (TRUE, BASE)]
        self.n = 3
        self.at = {}
        self.gadgets = []
        for bit in range(1, 12):
            self.new_bit(bit)
        for ci, originals in enumerate(clauses):
            lits = originals + (originals[-1],) * (3 - len(originals))
            d = 12 + ci
            self.new_bit(d)
            u, v, w = lits
            parts = []
            for targets in (
                (self.at[u], self.at[v], self.at[d]),
                (self.at[-d], self.at[w], FALSE),
            ):
                tri = tuple(range(self.n, self.n + 3))
                self.n += 3
                self.edges.extend(
                    (*pairwise(tri), (tri[-1], tri[0]), *zip(tri, targets))
                )
                parts.append((tri, targets))
            self.gadgets.append((d, lits, parts))
        self.pins = []
        for i in range(1, 9):
            leaf = self.n
            self.n += 1
            a = len(self.edges)
            self.edges.extend(((self.at[i], TRUE), (leaf, FALSE)))
            self.pins.append((a, a + 1, leaf))

    def new_bit(self, i):
        u, v = self.n, self.n + 1
        self.n += 2
        self.at[i] = u
        self.at[-i] = v
        self.edges.extend(((u, v), (u, BASE), (v, BASE)))

    def witness(self, bits):
        c = [-1] * self.n
        c[:3] = [FALSE, TRUE, BASE]
        for i, v in bits.items():
            c[self.at[i]] = v
            c[self.at[-i]] = 1 - v
        for d, lits, parts in self.gadgets:
            u, v, w = [literal(bits, l) for l in lits]
            h = next(
                h for h in range(2) if len({u, v, h}) > 1 and len({1 - h, w, 0}) > 1
            )
            c[self.at[d]] = h
            c[self.at[-d]] = 1 - h
            for tri, targets in parts:
                fill = next(
                    row
                    for row in PALETTE
                    if all(x != c[y] for x, y in zip(row, targets))
                )
                for p, x in zip(tri, fill):
                    c[p] = x
        for _, _, leaf in self.pins:
            c[leaf] = BASE
        assert min(c) >= 0
        return c


def check_coloring(order, colors):
    assert len(order) == len(colors)
    assert all(a != b for a, b in pairwise(colors))
    assert all(colors[a] != colors[b] for a, b in pairwise(order))


def audit_payload(payload, anchor):
    clauses = guarded_clauses(payload)
    source = PaletteGraph(clauses)
    enc = encode(source.n, source.edges)
    old = tuple(enc.permutation())
    base = compile_lane(old)
    bpos = {v: i for i, v in enumerate(enc.blue)}
    owner = {d: k for k, _, _, d, _ in enc.splitters}
    transpose = []
    for a, b, _ in source.pins:
        (td,) = [d for d in enc.matching[a] if owner[d] == TRUE]
        (fd,) = [d for d in enc.matching[b] if owner[d] == FALSE]
        transpose.append((bpos[td], bpos[fd], td, fd))
    # Find the beginning of the free lane on the physical target permutation.
    lane = base.index(site(2 + 2 * TIPS[0]))
    ntiles = len(old) + 6
    bit_fields = []
    for a, b, _, _ in transpose:
        bit_fields.append(
            tuple((lane + 7 * (a + 3) + j, lane + 7 * (b + 3) + j) for j in range(7))
        )
    groups = [
        {p for pairs in bit_fields[4 * i : 4 * i + 4] for ab in pairs for p in ab}
        for i in range(2)
    ]
    labels = [{base[p] for p in g} for g in groups]
    assert (
        all(len(g) == 56 for g in groups)
        and groups[0].isdisjoint(groups[1])
        and labels[0].isdisjoint(labels[1])
    )
    worlds = {}
    positives = 0
    for controls in product(range(6), repeat=2):
        models = []
        for a in product(range(2), repeat=2):
            bits = payload_bits(controls, a)
            if all(any(literal(bits, l) for l in clause) for clause in clauses):
                models.append(bits)
        payload_sat = any(
            all(literal(payload_bits(controls, a), l) for l in payload)
            for a in product(range(2), repeat=2)
        )
        S = sum(controls) % 6
        assert bool(models) == (S == 1 or S == 0 and payload_sat)
        bits = payload_bits(controls, (0, 0))
        on = [i for i in range(8) if bits[i + 1]]
        exchange = {}
        q = list(old)
        tree = list(base)
        delta = {}
        for i in on:
            a, b, td, fd = transpose[i]
            q[a], q[b] = q[b], q[a]
            exchange[td] = fd
            exchange[fd] = td
            for a, b in bit_fields[i]:
                tree[a], tree[b] = tree[b], tree[a]
                delta[a] = tree[a]
                delta[b] = tree[b]
        # Physical encoder equality, including untouched anchor, tiles and all free-lane fields.
        assert compile_lane(q) == tuple(tree)
        # Decode the identities of all seven-tip blocks directly from the native array.
        decoded = []
        for i in range(ntiles):
            offset = lane + 7 * i
            ids = [(v - site(2)) // 2 for v in tree[offset : offset + 7]]
            assert [j % 7 for j in ids] == list(TIPS) and len(
                {j // 7 for j in ids}
            ) == 1
            decoded.append(ids[0] // 7)
        assert decoded[:3] == [0, 1, 2] and decoded[3:-3] == [i + 3 for i in q]
        # Recover the source constraints from the switched blue incidence slots and untouched red pairs.
        data_owner = {enc.red[q[bpos[d]]]: k for d, k in owner.items()}
        actual = [frozenset((data_owner[a], data_owner[b])) for a, b in enc.matching]
        expected = list(map(frozenset, source.edges))
        for i in on:
            a, b, leaf = source.pins[i]
            expected[a] = frozenset((source.at[i + 1], FALSE))
            expected[b] = frozenset((leaf, TRUE))
        assert actual == expected
        if models:
            c = source.witness(models[0])
            assert all(c[u] != c[v] for u, v in actual)
            # Transport blue ownership of the data vertices while preserving every red slot.
            switched = replace(
                enc,
                blue=[exchange.get(x, x) for x in enc.blue],
                splitters=[
                    (k, u, v, exchange.get(d, d), tail)
                    for k, u, v, d, tail in enc.splitters
                ],
            )
            row = switched.extend(c)
            reduced = [row[v] for v in enc.red]
            check_coloring(q, reduced)
            full = extend_coloring(q, reduced, anchor)
            check_coloring(tree, full)
            positives += 1
        worlds[controls] = (bool(models), delta)
    couples = 0
    for b, (v, patch) in worlds.items():
        for i in range(2):
            alt = list(b)
            alt[i] = (alt[i] + (2 if v else 1) - sum(b)) % 6
            w, patch2 = worlds[tuple(alt)]
            assert w != v
            changed = {
                p
                for p in patch.keys() | patch2.keys()
                if patch.get(p, base[p]) != patch2.get(p, base[p])
            }
            assert changed and changed <= groups[i]
            adjacency = {
                j for p in changed for j in (p - 1, p) if 0 <= j < len(base) - 1
            }

            def edges_at(override, affected):
                return {
                    frozenset(
                        (override.get(j, base[j]), override.get(j + 1, base[j + 1]))
                    )
                    for j in affected
                }

            assert all(
                e & labels[i]
                for e in edges_at(patch, adjacency) ^ edges_at(patch2, adjacency)
            )
            couples += 1
    return len(enc.red), len(base), positives, couples


def audit():
    anchor = anchor_audit()
    for payload in ((10, 11), (10, -10)):
        n, m, yes, pairs = audit_payload(payload, anchor)
        print(
            f"{payload}: {n} former two-path entries, {m} final vertices, 36 full renders, "
            f"{yes} native positive colorings, {pairs} opposite-image couplings.",
            flush=True,
        )


if __name__ == "__main__":
    audit()
