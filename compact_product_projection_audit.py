"""A bit-once proper DIMACS projection of entries of AB-C over F2.

The input consists of three row-major square bit matrices. A model chooses
exactly one erroneous coordinate. Install pycosat to run the finite audit.
"""

from itertools import islice, product
from random import Random

import pycosat

from table_probe_context_audit import parse


def mask_name(bank, bits):
    return int(str(bank) + ''.join(str(bit) for bit in bits))


def recommended_chunk(side):
    t = side.bit_length() - 1
    return 1 << max(0, t.bit_length() - 1 - 3)


class ProductLayout:
    def __init__(self, side, chunk=None):
        assert side > 0 and side & (side - 1) == 0
        chunk = recommended_chunk(side) if chunk is None else chunk
        assert 1 <= chunk <= side and chunk & (chunk - 1) == 0
        self.side = side
        self.chunk = chunk
        self.library_limit = (2 * side + 2) * 10**chunk - 1
        self.variables = self.library_limit
        self.fixed = []
        self.lookups = []

        # The three common padding variables are forced false by forbidding
        # the other seven assignments. All later short clauses use these.
        for bits in product((0, 1), repeat=3):
            if any(bits):
                self.fixed.append(tuple(-i if bit else i
                                        for i, bit in enumerate(bits, 1)))
        self.true = self.fresh()
        self.add(self.true)
        width = side.bit_length() - 1
        low_width = chunk.bit_length() - 1
        self.row_bits = [self.fresh() for _ in range(width)]
        self.col_bits = [self.fresh() for _ in range(width)]
        row_low = self.decode(self.row_bits[:low_width])
        col_low = self.decode(self.col_bits[:low_width])
        row_high = self.decode(self.row_bits[low_width:])
        col_high = self.decode(self.col_bits[low_width:])
        row_full = self.decode(self.row_bits)

        a = [self.fresh() for _ in range(side)]
        b = [self.fresh() for _ in range(side)]
        c = self.fresh()
        names = set()
        for bank, (low, chosen) in enumerate(
                [(row_low, y) for y in a] + [(col_low, y) for y in b] + [(col_low, c)], 1):
            for mask in product((0, 1), repeat=chunk):
                name = mask_name(bank, mask)
                names.add(name)
                for indicator, value in zip(low, mask):
                    same = chosen if value else -chosen
                    self.add(-indicator, -same, name)
                    self.add(-indicator, same, -name)
        for name in range(4, self.library_limit + 1):
            if name not in names:
                self.add(-name)

        square = side * side
        for k in range(side):
            for group in range(side // chunk):
                start = group * chunk
                self.lookups.append(((-row_high[group],), 1 + k,
                                     [(start + l) * side + k for l in range(chunk)]))
                self.lookups.append(((-col_high[group],), 1 + side + k,
                                     [square + k * side + start + l for l in range(chunk)]))
        for i in range(side):
            for group in range(side // chunk):
                self.lookups.append(((-row_full[i], -col_high[group]), 2 * side + 1,
                                     [2 * square + i * side + group * chunk + l
                                      for l in range(chunk)]))

        terms = [self.and_gate(x, y) for x, y in zip(a, b)]
        parity = terms[0]
        for term in terms[1:]:
            result = self.fresh()
            self.add(parity, term, -result)
            self.add(parity, -term, result)
            self.add(-parity, term, result)
            self.add(-parity, -term, -result)
            parity = result
        self.add(parity, c)
        self.add(-parity, -c)
        header = f'p cnf {self.variables} {len(self.fixed) + len(self.lookups)}\n'
        self.prefix = header.encode() + b''.join(self.record(clause) for clause in self.fixed)

    def fresh(self):
        self.variables += 1
        return self.variables

    @staticmethod
    def proper(literals):
        distinct = list(dict.fromkeys(literals))
        assert not any(-lit in distinct for lit in distinct)
        for pad in (1, 2, 3):
            if len(distinct) == 3:
                break
            if pad not in distinct and -pad not in distinct:
                distinct.append(pad)
        assert len({abs(lit) for lit in distinct}) == 3
        return tuple(distinct)

    def add(self, *literals):
        self.fixed.append(self.proper(literals))

    def and_gate(self, x, y):
        z = self.fresh()
        self.add(-x, -y, z)
        self.add(x, -z)
        self.add(y, -z)
        return z

    def decode(self, bits):
        # Entry v is true precisely when the little-endian selector equals v.
        indicators = [self.true]
        for bit in bits:
            indicators = [self.and_gate(old, literal) for literal in (-bit, bit)
                          for old in indicators]
        return indicators

    @staticmethod
    def record(clause):
        return (' '.join(map(str, clause)) + ' 0\n').encode()

    def serialize(self, data):
        assert len(data) == 3 * self.side**2 and all(bit in (0, 1) for bit in data)
        encoded = bytearray(self.prefix)
        for guards, bank, indices in self.lookups:
            name = mask_name(bank, (data[index] for index in indices))
            encoded.extend(self.record(self.proper((*guards, name))))
        return bytes(encoded)


def product_bits(a, b, d):
    return [sum(a[i*d+k] * b[k*d+j] for k in range(d)) % 2
            for i in range(d) for j in range(d)]


def check_models(layout, data):
    d = layout.side
    area = d*d
    expected = {(i // d, i % d) for i, value in enumerate(
        product_bits(data[:area], data[area:2*area], d))
        if value != data[2*area+i]}
    clauses, variables = parse(layout.serialize(data))
    assert variables == layout.variables
    seen = set()
    for model in islice(pycosat.itersolve(clauses, vars=variables), len(expected) + 1):
        assignment = set(model)
        decode = lambda bits: sum(1 << j for j, var in enumerate(bits) if var in assignment)
        key = (decode(layout.row_bits), decode(layout.col_bits))
        assert key in expected and key not in seen
        seen.add(key)
    assert seen == expected
    return len(seen)


def check_projection(layout, data):
    base = layout.serialize(data)
    offsets = set()
    for index in range(len(data)):
        changed = data.copy()
        changed[index] ^= 1
        after = layout.serialize(changed)
        assert len(base) == len(after)
        positions = [p for p, (a, b) in enumerate(zip(base, after)) if a != b]
        assert len(positions) == 1
        pos, = positions
        assert base[pos] == ord('0') + data[index]
        assert after[pos] == ord('0') + changed[index]
        assert pos not in offsets
        offsets.add(pos)
    return len(offsets)


def main():
    rng = Random(3087)
    formulas = flips = models = 0
    for d, chunk in [(1, 1), (2, 1), (2, 2), (4, 2), (8, 2)]:
        layout = ProductLayout(d, chunk)
        area = d*d
        if d == 1:
            cases = [list(bits) for bits in product((0, 1), repeat=3)]
        else:
            cases = []
            for _ in range(2):
                a = [rng.randrange(2) for _ in range(area)]
                b = [rng.randrange(2) for _ in range(area)]
                correct = product_bits(a, b, d)
                for error_count in sorted({0, 1, 2, area // 2, area}):
                    c = correct.copy()
                    for error in rng.sample(range(area), error_count):
                        c[error] ^= 1
                    cases.append(a + b + c)
        for case in cases:
            models += check_models(layout, case)
        flips += check_projection(layout, list(cases[-1]))
        formulas += len(cases)
        print(f'd={d}, chunk={chunk}: {len(cases)} formulas, {len(layout.serialize(cases[0]))} bytes')
    print(f'{formulas} parsed formulas, {models} distinct models, {flips} independent low-bit flips.')


if __name__ == '__main__':
    main()
