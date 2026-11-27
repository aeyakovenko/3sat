"""Check the fixed-length decimal 3-CNF projection for two glued truth tables.

Run with Python 3 and pycosat. Bits are addressed least-significant first.
"""
from itertools import product
from random import Random

import pycosat


class Interface:
    def __init__(self, arity, low_bits):
        self.block_size = 1 << low_bits
        self.blocks = 1 << (arity - low_bits)
        reserved = 3 * 10**self.block_size - 1
        self.variables = reserved
        ports = [self.fresh() for _ in range(arity)]
        self.ports = ports
        self.parts = [[], []]
        self.slots = [[], []]
        flags_used = set()
        for side, fixed in enumerate(self.parts):
            false, guard, spare, root = (self.fresh() for _ in range(4))
            for a, b in product((1, -1), repeat=2):
                fixed.append((-false, a * guard, b * spare))
            fixed.extend((root, a * guard, b * spare) for a, b in product((1, -1), repeat=2))

            def indicators(bits):
                layer = [root]
                for port in reversed(bits):
                    next_layer = []
                    for parent in layer:
                        for literal in (-port, port):
                            child = self.fresh()
                            fixed.extend(((-child, parent, false), (-child, literal, false),
                                          (child, -parent, -literal)))
                            next_layer.append(child)
                    layer = next_layer
                return layer

            low = indicators(ports[:low_bits])
            high = indicators(ports[low_bits:])
            for mask in range(1 << self.block_size):
                flag = self.name(side, mask)
                flags_used.add(flag)
                for j, selector in enumerate(low):
                    fixed.append((-selector, flag if mask >> j & 1 else -flag, false))
            self.slots[side] = [(-selector, false) for selector in high]
            if side == 0:
                filler_guards = (guard, spare)
        guard, spare = filler_guards
        self.parts[0].extend((guard, var, spare) for var in range(1, reserved + 1)
                             if var not in flags_used)
        occurred = [{abs(lit) for clause in part for lit in clause} for part in self.parts]
        assert occurred[0] & occurred[1] == set(ports)
        assert occurred[0] | occurred[1] == set(range(1, self.variables + 1))

    def fresh(self):
        self.variables += 1
        return self.variables

    def name(self, side, mask):
        return int(str(side + 1) + format(mask, f"0{self.block_size}b"))

    def file(self, left, right):
        size = self.block_size
        mask = (1 << size) - 1
        clauses = []
        for side, table in enumerate((left, right)):
            clauses.extend(self.parts[side])
            for i, (selector, false) in enumerate(self.slots[side]):
                flag = self.name(side, (table >> (i * size)) & mask)
                clauses.append((selector, flag, false))
        field = len(str(self.variables)) + 1
        header = f"p cnf {self.variables} {len(clauses)}\n"
        body = "".join(f"{a:>{field}} {b:>{field}} {c:>{field}} 0\n" for a, b, c in clauses)
        return (header + body).encode("ascii")


def parse(file):
    header, *lines = file.decode("ascii").splitlines()
    p, cnf, v, count = header.split()
    assert (p, cnf) == ("p", "cnf") and len(lines) == int(count)
    clauses = []
    for line in lines:
        a, b, c, end = map(int, line.split())
        assert end == 0 and len({abs(a), abs(b), abs(c)}) == 3
        clauses.append([a, b, c])
    assert {abs(lit) for clause in clauses for lit in clause} == set(range(1, int(v) + 1))
    return clauses


def main():
    rng = Random(20261125)
    pairs = pins = changed = 0
    for k, low_bits in ((2, 1), (3, 1), (4, 1)):
        interface = Interface(k, low_bits)
        positions = 1 << k
        zero = interface.file(0, 0)
        columns = []
        for j in range(2 * positions):
            singleton = 1 << (j % positions)
            tweaked = interface.file(singleton if j < positions else 0,
                                     singleton if j >= positions else 0)
            assert len(tweaked) == len(zero)
            diffs = [i for i, (a, b) in enumerate(zip(zero, tweaked)) if a != b]
            assert len(diffs) == 1
            column, = diffs
            assert zero[column] == ord('0') and tweaked[column] == ord('1')
            columns.append(column)
        assert len(set(columns)) == len(columns)
        changed += len(columns)
        if k == 2:
            inputs = product(range(1 << positions), repeat=2)
        else:
            inputs = [(rng.getrandbits(positions), rng.getrandbits(positions)) for _ in range(24)]
            inputs.extend([(0, 0), ((1 << positions) - 1, 1), (1, 2)])
        for left, right in inputs:
            data = interface.file(left, right)
            expected_file = bytearray(zero)
            for j, column in enumerate(columns):
                if (left if j < positions else right) >> (j % positions) & 1:
                    expected_file[column] = ord('1')
            assert data == expected_file
            clauses = parse(data)
            assert (pycosat.solve(clauses) != 'UNSAT') == bool(left & right)
            pairs += 1
            for i in range(positions):
                fix = [[var if i >> bit & 1 else -var] for bit, var in enumerate(interface.ports)]
                assert (pycosat.solve(clauses + fix) != 'UNSAT') == bool(left & right & (1 << i))
                pins += 1
    print(f"{pairs} proper DIMACS files, {pins} pinned boundary decisions, {changed} projection columns")


if __name__ == "__main__":
    main()
