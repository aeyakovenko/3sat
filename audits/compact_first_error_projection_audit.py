"""Dense ternary DIMACS whose models mark errors first in both their row and column."""
from itertools import islice, product
from random import Random

import pycosat

from compact_product_projection_audit import ProductLayout, mask_name, product_bits, recommended_chunk
from table_probe_context_audit import parse


class FirstErrorLayout(ProductLayout):
    def __init__(self, side, chunk=None):
        assert side > 0 and side & (side - 1) == 0
        self.side = side
        self.chunk = h = recommended_chunk(side) if chunk is None else chunk
        assert 1 <= h <= side and h & (h - 1) == 0
        groups = side // h
        self.library_limit = (4 * side + 2 * groups + 1) * 10**h - 1
        self.variables = self.library_limit
        self.fixed = []
        self.lookups = []
        used = set()
        for bits in product((0, 1), repeat=3):
            if any(bits):
                self.fixed.append(tuple(-i if bit else i for i, bit in enumerate(bits, 1)))
        self.true = self.fresh()
        self.add(self.true)
        width = side.bit_length() - 1
        low_width = h.bit_length() - 1
        self.row_bits = [self.fresh() for _ in range(width)]
        self.col_bits = [self.fresh() for _ in range(width)]
        indices = []
        for bits in (self.row_bits, self.col_bits):
            indices.append((self.decode(bits[:low_width]), self.decode(bits[low_width:]),
                            self.decode(bits)))
        row, col = indices
        words = [tuple(mask) for mask in product((0, 1), repeat=h)]

        a, b, c_row, c_col = [[self.fresh() for _ in range(side)] for _ in range(4)]
        area = side * side
        bank = 0
        for wires, index, base, stride, step in (
            (a, row, 0, 1, side), (b, col, area, side, 1),
            (c_row, row, 2*area, 1, side), (c_col, col, 2*area, side, 1),
        ):
            low, high, _ = index
            for pos, wire in enumerate(wires):
                bank += 1
                for mask in words:
                    name = mask_name(bank, mask)
                    used.add(name)
                    for flag, value in zip(low, mask):
                        same = wire if value else -wire
                        self.add(-flag, -same, name)
                        self.add(-flag, same, -name)
                for g, flag in enumerate(high):
                    raw = [base + pos*stride + (g*h+l)*step for l in range(h)]
                    self.lookups.append(((-flag,), bank, 1, raw))

        for selected, line, full, base, stride, step in (
            (a, c_row, col[2], area, 1, side), (b, c_col, row[2], 0, side, 1),
        ):
            parity_banks = []
            for g in range(groups):
                bank += 1
                parity_banks.append(bank)
                for mask in words:
                    name = mask_name(bank, mask)
                    used.add(name)
                    if any(mask):
                        i = mask.index(1)
                        rest = mask[:i] + (0,) + mask[i+1:]
                        self.xor_into(name, mask_name(bank, rest), selected[g*h+i])
                    else:
                        self.add(-name)
            errors = []
            for pos in range(side):
                terms = []
                for g, lookup_bank in enumerate(parity_banks):
                    term = self.fresh()
                    terms.append(term)
                    raw = [base + pos*stride + (g*h+l)*step for l in range(h)]
                    self.lookups.append(((-term,), lookup_bank, 1, raw))
                    self.lookups.append(((term,), lookup_bank, -1, raw))
                folded = terms[0]
                for term in terms[1:]:
                    folded = self.xor_gate(folded, term)
                errors.append(self.xor_gate(folded, line[pos]))
            # Force the selected coordinate to be the first error on this line.
            earlier = -self.true
            for pos, (flag, error) in enumerate(zip(full, errors)):
                self.add(-flag, error)
                if pos:
                    self.add(-flag, -earlier)
                if pos + 1 < side:
                    earlier = -self.and_gate(-earlier, -error)

        assert bank == 4 * side + 2 * groups
        for label in range(4, self.library_limit + 1):
            if label not in used:
                self.add(-label)
        header = f'p cnf {self.variables} {len(self.fixed)+len(self.lookups)}\n'
        self.prefix = header.encode() + b''.join(self.record(row) for row in self.fixed)

    def xor_into(self, out, x, y):
        self.add(x, y, -out)
        self.add(x, -y, out)
        self.add(-x, y, out)
        self.add(-x, -y, -out)

    def xor_gate(self, x, y):
        z = self.fresh()
        self.xor_into(z, x, y)
        return z

    def serialize(self, data):
        assert len(data) == 3 * self.side**2 and all(x in (0, 1) for x in data)
        encoded = bytearray(self.prefix)
        for guards, bank, sign, indices in self.lookups:
            name = mask_name(bank, (data[i] for i in indices))
            encoded.extend(self.record(self.proper((*guards, sign*name))))
        return bytes(encoded)


def markers(data, d):
    a = d*d
    exact = product_bits(data[:a], data[a:2*a], d)
    delta = [u ^ v for u, v in zip(exact, data[2*a:])]
    selected = {(i,j) for i in range(d) for j in range(d)
                if delta[i*d+j] and not any(delta[i*d:i*d+j])
                and not any(delta[r*d+j] for r in range(i))}
    assert bool(selected) == any(delta)
    return selected


def audit_models(layout, data, projection):
    expected = markers(data, layout.side)
    zero, groups = projection
    physical = layout.serialize(data)
    predicted = bytearray(zero)
    for bit, positions in zip(data, groups):
        if bit:
            for pos in positions:
                predicted[pos] = ord('1')
    assert predicted == physical
    cnf, n = parse(physical)
    assert n == layout.variables
    seen = set()
    for model in islice(pycosat.itersolve(cnf, vars=n), len(expected) + 1):
        ones = set(model)
        def value(bits):
            return sum(1 << j for j, bit in enumerate(bits) if bit in ones)
        marker = value(layout.row_bits), value(layout.col_bits)
        assert marker in expected and marker not in seen
        seen.add(marker)
    assert seen == expected
    return len(seen)


def audit_flips(layout):
    data = [0] * (3 * layout.side**2)
    base = layout.serialize(data)
    seen = set()
    groups = []
    for i, old in enumerate(data):
        data[i] ^= 1
        after = layout.serialize(data)
        data[i] = old
        assert len(after) == len(base)
        # The fixed prefix is identical by serialization. Check every dynamic byte.
        begin = len(layout.prefix)
        offsets = [j for j in range(begin, len(after)) if after[j] != base[j]]
        assert len(offsets) == (3 if i < 2 * layout.side**2 else 2)
        assert not seen.intersection(offsets)
        for j in offsets:
            assert (base[j], after[j]) == (ord('0') + old, ord('0') + (old ^ 1))
        seen.update(offsets)
        groups.append(offsets)
    assert len(seen) == 8 * layout.side**2
    return base, groups


def tests(d, exhaustive, rng):
    if exhaustive:
        yield from product((0, 1), repeat=3*d*d)
        return
    for _ in range(2):
        a, b = ([rng.randrange(2) for _ in range(d*d)] for _ in range(2))
        exact = product_bits(a, b, d)
        for positions in [[], [0], [1, d], [0, 1, d, d+1],
                          [i*d+(d-1-i) for i in range(d)],
                          rng.sample(range(d*d), d*d//2), range(d*d)]:
            c = exact.copy()
            for t in positions:
                c[t] ^= 1
            yield a + b + c


def main():
    rng = Random(81472)
    total = 0
    for d, h, exhaustive in [(1,1,True), (2,1,True), (2,2,True), (4,2,False), (8,2,False)]:
        layout = FirstErrorLayout(d, h)
        models = files = 0
        projection = audit_flips(layout)
        for data in tests(d, exhaustive, rng):
            models += audit_models(layout, list(data), projection)
            files += 1
        varying = sum(map(len, projection[1]))
        total += files
        print(f'd={d} h={h}: {files} parsed formulas, {models} models, '
              f'{varying} disjoint physical data bits, {len(projection[0])} bytes',
              flush=True)
    print('Total files checked:', total)


if __name__ == '__main__':
    main()
