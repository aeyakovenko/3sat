"""Exhaust decimal mask lookups for a two-offset, two-group threshold cube.

Requires pycosat. Each SAT model identifies exactly one eligible block.
"""

from collections import Counter
from itertools import combinations, product
from math import comb

import pycosat

from table_probe_context_audit import parse


class Layout:
    def __init__(self, slots):
        assert slots in (2, 3)
        self.slots = slots
        self.threshold = (slots + 1) // 2
        self.masks = {}
        for q in range(slots):
            for mask in product((0, 1), repeat=2):
                self.masks[q, mask] = int(f"{q+1}{mask[0]}{mask[1]}")

        last_mask = max(self.masks.values())
        self.low = last_mask + 1
        self.high = last_mask + 2
        self.guesses = [last_mask+3+q for q in range(slots)]
        gate = self.guesses[-1] + 1
        # Seven forbidden tuples fix three distinct padding names to zero.
        rows = [tuple(-i if (v >> (i-1)) & 1 else i for i in (1, 2, 3))
                for v in range(1, 8)]
        used = set(self.masks.values())
        rows.extend((-i, 1, 2) for i in range(4, last_mask+1) if i not in used)
        for (q, mask), tag in self.masks.items():
            v = self.guesses[q]
            for offset, bit in enumerate(mask):
                inactive = self.low if offset == 0 else -self.low
                matches = v if bit else -v
                rows.extend(((inactive, -matches, tag), (inactive, matches, -tag)))
        if slots == 2:
            x, y = self.guesses
            rows.extend(((-x, gate, 1), (-y, gate, 1), (x, y, -gate)))
        else:
            for x, y in combinations(self.guesses, 2):
                rows.extend(((-x, -y, gate), (x, y, -gate)))
        rows.append((gate, 1, 2))

        records = [f"p cnf {gate} {len(rows)+2*slots}\n".encode()]
        records.extend((" ".join(map(str, row)) + " 0\n").encode() for row in rows)
        out = bytearray(b"".join(records))
        self.offsets = [None] * (4*slots)
        for group in range(2):
            inactive = self.high if group == 0 else -self.high
            for q in range(slots):
                out.extend(f"{inactive} {q+1}".encode())
                for offset in range(2):
                    bit = (2*group+offset)*slots+q
                    self.offsets[bit] = len(out)
                    out.extend(b"0")
                out.extend(b" 1 0\n")
        self.base = bytes(out)
        assert len(set(self.offsets)) == 4*slots and None not in self.offsets

    def file(self, mask):
        result = bytearray(self.base)
        for bit, offset in enumerate(self.offsets):
            result[offset] += (mask >> bit) & 1
        return bytes(result)

    def verify_models(self, mask, data):
        clauses, variables = parse(data)
        expected = set()
        for block in range(4):
            value = (mask >> (block*self.slots)) & ((1 << self.slots)-1)
            if value.bit_count() >= self.threshold:
                expected.add(block)
        observed = set()
        for assignment in pycosat.itersolve(clauses, vars=variables):
            positive = {v for v in assignment if v > 0}
            offset = int(self.low in positive)
            block = 2*int(self.high in positive)+offset
            assert block not in observed
            observed.add(block)
            values = [(mask >> (block*self.slots+q)) & 1 for q in range(self.slots)]
            assert [int(v in positive) for v in self.guesses] == values
            for (q, pattern), tag in self.masks.items():
                assert (tag in positive) == (values[q] == pattern[offset])
        assert observed == expected
        return len(observed)


def check(slots):
    layout = Layout(slots)
    m = len(layout.offsets)
    files = [layout.file(mask) for mask in range(1 << m)]
    model_counts = [layout.verify_models(mask, data) for mask, data in enumerate(files)]
    histogram = Counter(model_counts)
    passing = sum(comb(slots, j) for j in range(layout.threshold, slots+1))
    failing = (1 << slots)-passing
    assert histogram == {j: comb(4,j)*passing**j*failing**(4-j) for j in range(5)}

    verdict = [int(count > 0) for count in model_counts]
    coefficient = sum((-1)**(m-mask.bit_count()) * val for mask, val in enumerate(verdict))
    assert coefficient == -comb(slots-1, layout.threshold-1)**4
    # Fix the increasing physical-word scan and the last editable coordinate
    # in its final varying word. These opposite-verdict pairs are disjoint.
    last_bit = max(range(m), key=layout.offsets.__getitem__)
    edges = pivotal = last_pivotal = 0
    for mask, data in enumerate(files):
        for bit, byte in enumerate(layout.offsets):
            if mask & (1 << bit):
                continue
            neighbor = mask | (1 << bit)
            assert data[byte] == ord("0")
            assert files[neighbor] == data[:byte] + b"1" + data[byte+1:]
            edges += 1
            if verdict[mask] != verdict[neighbor]:
                pivotal += 1
                last_pivotal += int(bit == last_bit)
    assert edges == m * (1 << (m-1))
    assert last_pivotal == comb(slots-1, layout.threshold-1)*failing**3
    assert pivotal == m * last_pivotal and last_pivotal >= abs(coefficient)
    clauses, variables = parse(layout.base)
    print(f"blocks=4 slots={slots} threshold={layout.threshold}: "
          f"{len(layout.base)} bytes, {variables} names, {len(clauses)} proper clauses")
    print(f"  {len(files)} files, {sum(verdict)} SAT, {sum(model_counts)} models; "
          f"model multiplicities {dict(sorted(histogram.items()))}")
    print(f"  {edges} one-bit edges, {pivotal} pivotal, {last_pivotal} last-bit pairs, "
          f"top coefficient {coefficient}")


if __name__ == "__main__":
    for width in (2, 3):
        check(width)
