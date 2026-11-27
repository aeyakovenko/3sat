"""Finite checks for tight-size-of-syntactic-read-k-sat.md. Requires pycosat."""

from itertools import islice, product

import pycosat

from table_probe_context_audit import parse


def rank(rows):
    pivots = {}
    for row in rows:
        while row:
            column = row.bit_length() - 1
            if column not in pivots:
                pivots[column] = row
                break
            row ^= pivots[column]
    return len(pivots)


def audit_rectangles(side):
    """Maximize over all monochromatic rectangles by choosing the row set."""
    size = 1 << side
    universe = (1 << size) - 1
    checks = 0
    for matrix in product(range(size), repeat=side):
        dimension = rank(matrix)
        right_values = [sum(((y & row).bit_count() % 2) << i
                            for i, row in enumerate(matrix))
                        for y in range(size)]
        for left_shift, right_shift in product(range(size), repeat=2):
            masks = []
            for x in range(size):
                masks.append(sum(((((x & value).bit_count()
                                     + (left_shift & x).bit_count()
                                     + (right_shift & y).bit_count()) % 2) << y)
                                 for y, value in enumerate(right_values)))
            for color in (0, 1):
                allowed = masks if color else [universe ^ m for m in masks]
                common = [universe]
                for subset in range(1, 1 << size):
                    bit = subset & -subset
                    choices = common[subset ^ bit] & allowed[bit.bit_length()-1]
                    assert subset.bit_count() * choices.bit_count() <= size * size >> dimension
                    common.append(choices)
                checks += 1
    return checks


def formula(matrix, bits):
    m = len(matrix)
    clauses = [tuple(-i if bit else i for i, bit in enumerate(v, 1))
               for v in product(range(2), repeat=3) if any(v)]

    def emit(*lits):
        clauses.append(tuple(lits) + (1, 2)[:3-len(lits)])

    last = 20*m + 1
    used = {1, 2, 3}
    for i, bit in enumerate(bits, 1):
        zero, one = 10*i, 10*i+1
        used.update((zero, one))
        emit(zero, one)
        emit(-zero, -one)
        emit(zero+bit)
    for i in range(4, last+1):
        if i not in used:
            emit(-i)
    last += 1
    acc = last
    emit(-acc)
    for i, row in enumerate(matrix):
        for j in range(m):
            if row >> j & 1:
                a, b = 10*(i+1)+1, 10*(m+j+1)+1
                edge, new = last+1, last+2
                last = new
                emit(-a, -b, edge)
                emit(a, -edge)
                emit(b, -edge)
                emit(acc, edge, -new)
                emit(acc, -edge, new)
                emit(-acc, edge, new)
                emit(-acc, -edge, -new)
                acc = new
    emit(-acc)
    records = [' '.join(map(str, c)) + ' 0' for c in clauses]
    return ('p cnf ' + str(last) + ' ' + str(len(clauses))
            + '\n' + '\n'.join(records) + '\n').encode()


def audit_files():
    files = edits = 0
    for matrix in ((1,), (0, 1), (1, 2), (3, 3), (3, 6, 5)):
        m = len(matrix)
        zero = (0,) * (2*m)
        reference = formula(matrix, zero)
        pins = []
        for i in range(2*m):
            file = formula(matrix, zero[:i] + (1,) + zero[i+1:])
            delta = [(j, a, b) for j, (a, b) in enumerate(zip(reference, file)) if a != b]
            assert len(file) == len(reference) and len(delta) == 1
            j, changed_from, changed_to = delta[0]
            assert (changed_from, changed_to) == (48, 49)
            pins.append(j)
        assert len(set(pins)) == 2*m
        for bits in product(range(2), repeat=2*m):
            file = formula(matrix, bits)
            expected = bytearray(reference)
            for position, bit in zip(pins, bits):
                expected[position] += bit
            assert file == expected
            clauses, variables = parse(file)
            models = list(islice(pycosat.itersolve(clauses, vars=variables), 2))
            y = sum(bit << i for i, bit in enumerate(bits[m:]))
            parity = sum(x * (row & y).bit_count() for x, row in zip(bits, matrix)) % 2
            assert len(models) == 1 - parity
            files += 1
            edits += 2*m
    return files, edits


if __name__ == '__main__':
    print('matrix/affine-offset/verdict combinations:', sum(audit_rectangles(n) for n in (1, 2, 3)))
    print('parsed files, directed one-bit edits:', *audit_files())
