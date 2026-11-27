"""Audit the clause tree, its private assignments and physical one-bit edits. Requires pycosat."""

from collections import Counter, defaultdict
from itertools import product
import pycosat


def lit_value(lit, model):
    return model[abs(lit)] == (lit > 0)


def simplify(formula):
    if () in formula:
        return [(1,), (-1,)]
    normalized = []
    for clause in formula:
        row = tuple(dict.fromkeys(clause))
        if any(-lit in row for lit in row):
            continue
        if row not in normalized:
            normalized.append(row)
    return normalized


def occurrence_copies(source):
    groups = defaultdict(list)
    copied = []
    last = 0
    for row in simplify(source):
        new_row = []
        for lit in row:
            last += 1
            new_row.append(last if lit > 0 else -last)
            groups[abs(lit)].append(last)
        copied.append(tuple(new_row))
    for names in groups.values():
        if len(names) > 1:
            copied.extend((-u, v) for u, v in zip(names, names[1:]+names[:1]))
    return copied


class ClauseTree:
    def __init__(self, source):
        clean = simplify(source)
        n = max((abs(lit) for row in clean for lit in row), default=0)
        left = [row for row in clean if min(row) > 0] + [(n+1,)]
        right = [row for row in clean if min(row) < 0] + [(-n-2,)]
        self.leaves = left + right
        self.cut = len(left)
        self.payload_vars = n+2
        self.var_count = n+2
        self.children = [()] * len(self.leaves)
        self.parent = {}
        self.raw = []
        self.kinds = []
        self.physical = []
        self.which = []
        self.pad = {}

        def merge(a, b):
            u = len(self.children)
            self.children.append((a, b))
            self.parent[a] = self.parent[b] = u
            return u

        def build(start, stop):
            if stop-start == 1:
                return start
            mid = (start+stop)//2
            return merge(build(start, mid), build(mid, stop))

        self.root = merge(build(0, self.cut), build(self.cut, len(self.leaves)))
        self.interval = {}
        self.rep = {}
        clock = 0

        def number(u):
            nonlocal clock
            start = clock
            clock += 1
            for v in self.children[u]:
                number(v)
            self.interval[u] = (start, clock)
            self.rep[u] = self.rep[self.children[u][0]] if self.children[u] else u

        number(self.root)
        child_order = sorted(self.parent, key=lambda u: self.interval[u][0])
        self.message = {(u, self.parent[u]): self.fresh() for u in child_order}
        self.message.update({(self.parent[u], u): self.fresh() for u in child_order})
        for i, row in enumerate(self.leaves):
            p = self.parent[i]
            y, incoming = self.message[i, p], self.message[p, i]
            self.add((incoming,) + row, ('A', i))
            for lit in row:
                self.add((-y, incoming, -lit), ('B', i, lit))
        for u, kids in enumerate(self.children):
            if not kids:
                continue
            l, r = kids
            nbrs = list(kids) + ([self.parent[u]] if u in self.parent else [])
            self.add((-self.message[l, u], -self.message[r, u]), ('H', u))
            for v in nbrs:
                self.add((-self.message[u, v],) + tuple(self.message[w, u] for w in nbrs if w != v),
                         ('R', u, v))

        # Allow a subtree interval to mask precisely the appropriate four-literal pads.
        first_pad = min(self.pad.values())
        order = sorted(self.pad, key=lambda i: (len(self.raw[i]), i))
        new_pad = {i: first_pad+j for j, i in enumerate(order)}
        rename = {self.pad[i]: new_pad[i] for i in order}
        self.pad = new_pad
        self.physical = [tuple((1 if x > 0 else -1)*rename.get(abs(x), abs(x))
                               for x in row) for row in self.physical]
        self.leaf_pad = {self.kinds[i][1]: z for i, z in self.pad.items() if len(self.raw[i]) == 4}

    def fresh(self):
        self.var_count += 1
        return self.var_count

    def add(self, row, kind):
        i = len(self.raw)
        self.raw.append(row)
        self.kinds.append(kind)
        if len(row) == 3:
            pieces = [row]
        else:
            z = self.fresh()
            self.pad[i] = z
            if len(row) == 2:
                pieces = [row+(z,), row+(-z,)]
            else:
                assert len(row) == 4
                pieces = [row[:2]+(z,), (-z,)+row[2:]]
        for j, piece in enumerate(pieces):
            assert len(set(map(abs, piece))) == 3
            self.which.append((i, j))
            self.physical.append(piece)

    def inside(self, node, subtree):
        start, stop = self.interval[subtree]
        return start <= self.interval[node][0] < stop

    def source_side(self, origin, arc):
        a, b = arc
        if self.parent.get(a) == b:
            return self.inside(origin, a)
        assert self.parent.get(b) == a
        return not self.inside(origin, b)

    def descriptor(self, deleted):
        i, _ = self.which[deleted]
        kind, *indices = self.kinds[i]
        default = False
        sources = []
        fake = None
        overrides = {}
        if kind in ('A', 'B'):
            leaf = indices[0]
            sources = [leaf]
            for lit in self.leaves[leaf]:
                make_true = kind == 'B' and lit == indices[-1]
                overrides[abs(lit)] = (lit > 0) == make_true
        elif kind == 'H':
            sources = [self.rep[v] for v in self.children[indices[0]]]
        else:
            assert kind == 'R'
            u, v = fake = tuple(indices)
            if v in self.children[u]:
                sources = [self.rep[v]]
            else:
                default = self.rep[u] < self.cut
        return default, sources, fake, overrides

    def private(self, deleted):
        i, j = self.which[deleted]
        default, sources, fake, overrides = self.descriptor(deleted)
        model = [default] * (self.var_count+1)
        for var, value in overrides.items():
            model[var] = value
        for arc, var in self.message.items():
            value = any(self.source_side(s, arc) for s in sources)
            if fake and not value:
                u, v = fake
                a, b = arc
                in_component = not self.source_side(a, fake) and not self.source_side(b, fake)
                value = arc == fake or (in_component and self.source_side(u, arc))
            model[var] = value
        for parent_row, z in self.pad.items():
            row = self.raw[parent_row]
            if parent_row == i:
                model[z] = bool(j)
            else:
                model[z] = len(row) == 4 and not any(lit_value(lit, model) for lit in row[:2])
        return model

    def verify_packed(self, deleted, model, width=8):
        default, sources, fake, overrides = self.descriptor(deleted)
        up_fake = fake is not None and self.parent.get(fake[0]) == fake[1]
        base = [False] + [default]*self.payload_vars + [False]*(self.var_count-self.payload_vars)
        for child, par in self.parent.items():
            base[self.message[par, child]] = not (up_fake and self.inside(child, fake[0]))
        if up_fake:
            for i, z in self.pad.items():
                if len(self.raw[i]) == 4 and self.inside(self.kinds[i][1], fake[0]):
                    base[z] = not lit_value(self.raw[i][1], base)

        exceptions = set(overrides)
        raw_index, _ = self.which[deleted]
        if raw_index in self.pad:
            exceptions.add(self.pad[raw_index])
        for u in sources:
            if u in self.leaf_pad:
                exceptions.add(self.leaf_pad[u])
        for u in sources + ([fake[0]] if up_fake else []):
            while u in self.parent:
                par = self.parent[u]
                exceptions.update((self.message[par, u], self.message[u, par]))
                u = par
        masks = defaultdict(int)
        for var in exceptions:
            if model[var] != base[var]:
                masks[var//width] |= 1 << (var % width)
        checked = 0
        for offset in range(1, self.var_count+1):
            # Include reads straddling a block boundary. Bit zero is reserved.
            expected = sum(model[i] << (i-offset)
                           for i in range(offset, min(offset+width, len(model))))
            template = sum(base[i] << (i-offset)
                           for i in range(offset, min(offset+width, len(model))))
            block = offset//width
            correction = masks[block] | (masks[block+1] << width)
            correction = (correction >> (offset % width)) & ((1 << width)-1)
            assert template ^ correction == expected
            checked += 1
        return checked

    def serialized(self):
        data = bytearray(f'p cnf {10*self.var_count+3} {len(self.physical)}\n'.encode())
        positions = []
        for row in self.physical:
            for lit in row:
                data.extend(b' '*24)
                token = ('' if lit > 0 else '-') + str(10*abs(lit)+2)
                data.extend(token.encode())
                positions.append(len(data)-1)
            data.extend(b' 0\n')
        assert all(i//8 != j//8 for i, j in zip(positions, positions[1:]))
        return data, positions


def source_suite():
    base = [(), (1,), (-1,), (2,), (-2,), (1, 2), (-1, -2), (1, -2),
            (1, 1, -2), (1, -1, 2), (1, 2, 3), (-1, -2, -3)]
    yield ()
    for row in base:
        yield (row,)
    yield from product(base, repeat=2)
    full_cube = tuple(tuple(s*i for i, s in enumerate(signs, 1))
                      for signs in product((-1, 1), repeat=3))
    yield full_cube
    for k in range(len(full_cube)):
        yield full_cube[:k]+full_cube[k+1:]


def check_physical_edits(tree):
    data, positions = tree.serialized()
    checked = 0
    for pos in positions:
        assert data[pos] == ord('2')
        data[pos] ^= 1
        rows = [tuple(map(int, line.split()[:-1])) for line in data.splitlines()[1:]]
        assert pycosat.solve(rows) != 'UNSAT'
        data[pos] ^= 1
        checked += 1
    return checked


def inverse_split(rows, pivot):
    pair = [r for r in rows if pivot in r or -pivot in r]
    assert len(pair) == 2 and any(pivot in r for r in pair) and any(-pivot in r for r in pair)
    literals = {lit for r in pair for lit in r if abs(lit) != pivot}
    assert len(literals) == len(set(map(abs, literals))) == 3
    return [r for r in rows if r not in pair] + [tuple(literals)]


def row_multiset(rows):
    return sorted(tuple(sorted(row)) for row in rows)


def inverse_split_checks():
    overlaps = disjoint = 0
    for x, y, b in product((-1, 1), (-2, 2), (-3, 3)):
        for a, c in product((-6, -5, -4, 4, 5, 6), repeat=2):
            old = [(x, y, b), (-x, b, a), (-y, b, c), (4, 5, 6), (4, 5, 6)]
            left = inverse_split(old, abs(x))
            right = inverse_split(old, abs(y))
            rename = {y: -x, -y: x}
            renamed = [tuple(rename.get(lit, lit) for lit in row) for row in left]
            assert row_multiset(renamed) == row_multiset(right)
            overlaps += 1
    for b, a, c, d in product((-3, 3), (-4, 4), (-5, 5), (-6, 6)):
        old = [(1, b, a), (-1, b, c), (2, b, a), (-2, b, d), (a, b, c)]
        left = inverse_split(inverse_split(old, 1), 2)
        right = inverse_split(inverse_split(old, 2), 1)
        assert row_multiset(left) == row_multiset(right)
        disjoint += 1
    print(f'inverse-split overlaps {overlaps}, commuting disjoint pivots {disjoint}')


def main():
    formulas = negatives = private = physical = packed = 0
    inverse_split_checks()
    kinds = set()
    maximum_occurrences = 0
    for formula in source_suite():
        tree = ClauseTree(formula)
        positive = pycosat.solve(formula) != 'UNSAT'
        assert positive == (pycosat.solve(tree.physical) != 'UNSAT')
        bounded = ClauseTree(occurrence_copies(formula))
        assert positive == (pycosat.solve(bounded.physical) != 'UNSAT')
        occurrences = Counter(abs(lit) for row in bounded.physical for lit in row)
        maximum_occurrences = max(maximum_occurrences, max(occurrences.values()))
        assert max(occurrences.values()) <= 7
        for index, row in enumerate(tree.physical):
            model = tree.private(index)
            packed += tree.verify_packed(index, model)
            failed = [j for j, clause in enumerate(tree.physical)
                      if not any(lit_value(lit, model) for lit in clause)]
            assert failed == [index]
            raw_index, _ = tree.which[index]
            kinds.add(tree.kinds[raw_index][0])
            # Each literal can independently repair the unique failing row.
            for lit in row:
                assert lit_value(-lit, model)
            private += 1
        if formula in (((),), ((1,), (-1,))) or len(formula) == 8:
            assert not positive
            physical += check_physical_edits(tree)
        negatives += int(not positive)
        formulas += 1
    assert kinds == {'A', 'B', 'H', 'R'}
    print(f'formulas {formulas}, negative centers {negatives}, private physical-clause models {private}')
    print(f'literal sign repairs certified {3*private}, serialized one-bit SAT repairs {physical}')
    print(f'bounded-occurrence images {formulas}, maximum occurrences {maximum_occurrences}')
    print(f'packed reads at arbitrary bit offsets {packed}')


if __name__ == '__main__':
    main()
