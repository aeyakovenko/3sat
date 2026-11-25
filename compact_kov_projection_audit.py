"""Check the projected DIMACS file, including model multiplicities. Requires pycosat."""

from itertools import islice, product
from random import Random

import pycosat

from compact_product_projection_audit import ProductLayout, mask_name
from table_probe_context_audit import parse


def build(k, size, dim, chunk):
    """Return a fixed proper file, its pin offsets, and selector IDs for a given shape."""
    width = (size - 1).bit_length()
    capacity = 1 << width
    assert k >= 2 and size >= 1 and dim >= 1
    assert 1 <= chunk <= capacity and chunk & (chunk - 1) == 0
    limit = (k * dim + 1) * 10**chunk - 1
    variables = limit
    clauses = [tuple(-i if bit else i for i, bit in enumerate(v, 1))
               for v in product((0, 1), repeat=3) if any(v)]

    def fresh():
        nonlocal variables
        variables += 1
        return variables

    def emit(*literals):
        clauses.append(ProductLayout.proper(literals))

    def and_gate(a, b):
        c = fresh()
        emit(-a, -b, c)
        emit(a, -c)
        emit(b, -c)
        return c

    true = fresh()
    emit(true)

    def decode(bits):
        flags = [true]
        for bit in bits:
            flags = [and_gate(flag, signed) for signed in (-bit, bit) for flag in flags]
        return flags

    low_width = chunk.bit_length() - 1
    selectors = [[fresh() for _ in range(width)] for _ in range(k)]
    results = [[fresh() for _ in range(dim)] for _ in range(k)]
    names = set()
    data = []
    for party, bits in enumerate(selectors):
        low, high = decode(bits[:low_width]), decode(bits[low_width:])
        for group, selected in enumerate(high):
            start = group * chunk
            if start >= size:
                emit(-selected)
            elif start + chunk > size:
                for lane in range(size - start, chunk):
                    emit(-selected, -low[lane])
        for j in range(dim):
            bank = 1 + dim * party + j
            bit = results[party][j]
            for mask in product((0, 1), repeat=chunk):
                name = mask_name(bank, mask)
                names.add(name)
                for lane, value in enumerate(mask):
                    right = bit if value else -bit
                    emit(-low[lane], -right, name)
                    emit(-low[lane], right, -name)
            for group, selected in enumerate(high):
                if group * chunk < size:
                    data.append((party, j, group, bank, selected))
    for v in range(4, limit + 1):
        if v not in names:
            emit(-v)
    for j in range(dim):
        acc = results[0][j]
        for party in range(1, k):
            acc = and_gate(acc, results[party][j])
        emit(-acc)

    out = bytearray(f'p cnf {variables} {len(clauses)+len(data)}\n'.encode())
    out.extend(b' ' * size + b'\n' + b' ' * dim + b'\n')
    for clause in clauses:
        out.extend(ProductLayout.record(clause))
    pins = [None] * (k * size * dim)
    for party, j, group, bank, selected in data:
        prefix = f'-{selected} {bank}'.encode()
        out.extend(prefix)
        for lane in range(chunk):
            i = group * chunk + lane
            if i < size:
                pins[(party * size + i) * dim + j] = len(out)
            out.extend(b'0')
        out.extend(b' 1 0\n')
    assert None not in pins and len(set(pins)) == len(pins)
    return out, pins, selectors


def audit_case(shape, trials):
    k, size, dim, chunk = shape
    template, pins, selectors = build(*shape)
    rng = Random(4100 + k + 30*size + 211*dim)
    if trials is None:
        inputs = product(range(2), repeat=len(pins))
    else:
        inputs = [[v] * len(pins) for v in (0, 1)]
        inputs += [[rng.randrange(2) for _ in pins] for _ in range(trials)]
    cases = models = 0
    for data in inputs:
        file = bytearray(template)
        for offset, bit in zip(pins, data):
            assert file[offset] == 48
            file[offset] += bit
        clauses, declared = parse(bytes(file))
        expected = set()
        for ids in product(range(size), repeat=k):
            if all(any(not data[(p * size + i) * dim + j] for p, i in enumerate(ids))
                   for j in range(dim)):
                expected.add(ids)
        observed = []
        for assignment in islice(pycosat.itersolve(clauses, vars=declared), len(expected)+1):
            positive = {v for v in assignment if v > 0}
            observed.append(tuple(sum(1 << b for b, v in enumerate(group) if v in positive)
                                  for group in selectors))
        assert len(observed) == len(expected) and set(observed) == expected
        cases += 1
        models += len(observed)
    return cases, models


def low_space_count(lists, dim):
    """Stream over high-coordinate subsets, recycling the low-coordinate tables."""
    size = len(lists[0])
    b = min(dim, size.bit_length() - 1)
    cap = 1 << b
    total = 0
    for head in range(1 << (dim - b)):
        tables = []
        for rows in lists:
            table = [0] * cap
            for row in rows:
                if (row >> b) & head == head:
                    table[row & (cap-1)] += 1
            for i in range(b):
                for tail in range(cap):
                    if not (tail >> i & 1):
                        table[tail] += table[tail | (1 << i)]
            tables.append(table)
        for tail in range(cap):
            term = (-1) ** (head.bit_count() + tail.bit_count())
            for table in tables:
                term *= table[tail]
            total += term
    return total


if __name__ == '__main__':
    counts = [audit_case(shape, trials) for shape, trials in [
        ((4, 1, 2, 1), None), ((4, 2, 1, 2), None), ((4, 3, 2, 2), 12),
        ((3, 3, 2, 2), 10), ((2, 5, 3, 2), 5), ((5, 2, 2, 1), 8)]]
    rng = Random(282)
    for i in range(240):
        k, size, dim = 2+i%4, 1+i%5, 1+i%9
        lists = [[rng.getrandbits(dim) for _ in range(size)] for _ in range(k)]
        count = 0
        for rows in product(*lists):
            intersection = (1 << dim)-1
            for row in rows:
                intersection &= row
            count += intersection == 0
        assert low_space_count(lists, dim) == count
    print('parsed files:', sum(n for n, _ in counts), 'full models:', sum(n for _, n in counts))
    print('blocked subset-transform instances:', 240)
