"""Check sparse DIMACS renaming, virtual byte access, phase entropy, and FLMV slack."""
from fractions import Fraction
from itertools import product
from math import ceil
from random import Random


def name(index, bits, gap):
    binary = f'{index:0{bits}b}'
    assert len(binary) == bits
    return '1' + ''.join('0' * (gap - 1) + bit for bit in binary)


def word_bytes(length_in_bits, coefficient):
    # 2^(16 k q) >= (N+2)^p for D=p/q.
    needed = ((length_in_bits + 2) ** coefficient.numerator - 1).bit_length()
    return 2 * ceil(Fraction(needed, 16 * coefficient.denominator))


def emit(clauses, bits, gap):
    bound = name((1 << bits) - 1, bits, gap)
    preamble = f'p cnf {bound} {len(clauses)}\n'
    body = ''.join(''.join(('-' if v < 0 else ' ') + name(abs(v), bits, gap) + ' '
                           for v in clause) + '0\n' for clause in clauses)
    return preamble, body


def slot(offset, bits, gap):
    """Locate a fixed byte, sign or single binary source bit in one clause."""
    field = gap * bits + 3
    literal, pos = divmod(offset, field)
    if literal == 3:
        return '0\n'[pos], None, None
    if pos == 0:
        return None, literal, 'sign'
    if pos == 1 or pos == field - 1:
        return '1' if pos == 1 else ' ', None, None
    group, within = divmod(pos - 2, gap)
    if within == gap - 1:
        return None, literal, bits - 1 - group
    return '0', None, None


def audit(coefficient, bits, gap, clauses):
    preamble, body = emit(clauses, bits, gap)
    stride = 3 * (gap * bits + 3) + 2
    assert len(body) == stride * len(clauses)
    file = preamble + body
    width = word_bytes(len(file) * 8, coefficient)
    layout = [slot(i, bits, gap) for i in range(stride)]
    for i, raw in enumerate(body):
        row, position = divmod(i, stride)
        fixed, literal, bit = layout[position]
        if fixed is None:
            value = clauses[row][literal]
            fixed = ('-' if value < 0 else ' ') if bit == 'sign' else str((abs(value) >> bit) & 1)
        assert fixed == raw

    by_phase = {}
    for address in range(0, len(file) - width + 1, width):
        if address >= len(preamble):
            phase = (address - len(preamble)) % stride
            by_phase.setdefault(phase, set()).add(file[address:address + width])
    for phase in range(stride):
        hot = sum(layout[(phase + i) % stride][0] is None for i in range(width))
        # Split at clause boundaries. Every partial or full literal field
        # adds at most one sign and less than one excess digit beyond width/gap.
        field_fragments = set()
        for i in range(phase, phase + width):
            row, offset = divmod(i, stride)
            col = offset // (gap * bits + 3)
            if col < 3:
                field_fragments.add((row, col))
        assert hot <= Fraction(width, gap) + 2 * len(field_fragments)
        assert len(by_phase.get(phase, ())) <= 1 << hot

    renaming = {abs(v): int(name(abs(v), bits, gap)) for row in clauses for v in row}
    assert len(set(renaming.values())) == len(renaming)
    assert all(0 < v <= int(preamble.split()[2]) for v in renaming.values())
    parsed = [[int(word) for word in line.split()] for line in body.splitlines()]
    for before, after in zip(clauses, parsed):
        assert after == [(-1 if v < 0 else 1) * renaming[abs(v)] for v in before] + [0]
    if len(renaming) <= 6:
        labels = list(renaming)
        for truth in product((False, True), repeat=len(labels)):
            src = dict(zip(labels, truth))
            dst = {renaming[i]: src[i] for i in labels}
            sat = lambda rows, val: all(any(val[abs(v)] == (v > 0) for v in row) for row in rows)
            assert sat(clauses, src) == sat([row[:-1] for row in parsed], dst)


def main():
    rng = Random(11235)
    completed = 0
    for d in (Fraction(1), Fraction(3, 2), Fraction(9, 4), Fraction(5), Fraction(32)):
        for bits in (2, 5, 11):
            source = [i for i in range(1, 1 << bits)]
            dense = list(product((-3, -2, -1, 1, 2, 3), repeat=3)) if bits == 2 else [
                tuple(rng.choice(source) * rng.choice((-1, 1)) for _ in range(3)) for _ in range(201)]
            for gap in (2, 2 * ceil(d)):
                audit(d, bits, gap, dense)
                completed += 1
        assert d / (8 * (2 * ceil(d))) <= Fraction(1, 16)
    c = Fraction(1201, 1000)
    forbidden_space = ((c + 2) / c**2 - c) / 2
    actual_space = Fraction(1, 16) + 2 * Fraction(1, 5)
    assert actual_space == Fraction(37, 80) < Fraction(464, 1000)
    assert forbidden_space > Fraction(509, 1000)
    print(f'{completed} layouts checked across five width coefficients')
    print(f'alpha={float(actual_space)}, FLMV d(1.201)={float(forbidden_space):.9f}')


if __name__ == '__main__':
    main()
