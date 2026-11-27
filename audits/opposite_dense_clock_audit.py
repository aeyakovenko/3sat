"""Finite checks of complementary proper DIMACS files and erasure recovery."""
from itertools import product
from compiled_horn_receipt_audit import Circuit, exact_sat


def dot(a, x):
    return (a & x).bit_count() % 2


def xor(net, a, b):
    z = net.fresh()
    for left, right in product(range(2), repeat=2):
        net.add(-a if left else a, -b if right else b, z if left ^ right else -z)
    return z


def block_product(net, inputs, rows, width):
    tables = []
    for start in range(0, len(inputs), width):
        bank = inputs[start:start + width]
        table = [-net.one]
        for mask in range(1, 1 << len(bank)):
            old = mask & (mask - 1)
            extra = bank[(mask ^ old).bit_length() - 1]
            table.append(xor(net, table[old], extra) if old else extra)
        tables.append(table)
    outputs = []
    for row in rows:
        acc = -net.one
        for block, table in enumerate(tables):
            term = table[(row >> (block * width)) & (len(table) - 1)]
            if term != -net.one:
                acc = term if acc == -net.one else xor(net, acc, term)
        outputs.append(acc)
    return outputs


def primal_dual():
    tests = 0
    for a0, a1, b in product(range(4), repeat=3):
        a = (a0, a1)
        transpose = [sum((row >> j & 1) << i for i, row in enumerate(a)) for j in range(2)]
        expected = any(all(dot(row, x) == b >> i & 1 for i, row in enumerate(a)) for x in range(4))
        verdicts = []
        for rows, rhs in [(a, b), ([*transpose, b], 4)]:
            net = Circuit(True)
            outputs = block_product(net, [net.fresh(), net.fresh()], rows, 2)
            for i, output in enumerate(outputs):
                net.add(output if rhs >> i & 1 else -output)
            raw = padded(net)
            verdicts.append(exact_sat(raw))
        assert verdicts == [expected, not expected]
        tests += 2
    return tests


def padded(net):
    raw = net.bytes()
    assert raw.endswith(b' 0\n') and len(raw) <= 8192
    return raw[:-2] + b' ' * (8192 - len(raw)) + raw[-2:]


def noisy_file(A, y, d, k, u, polarity):
    net = Circuit(True)
    pairs = [(10 * (j + 1) + 2, 10 * (j + 1) + 3) for j in range(d + 1)]
    selected = {z for pair in pairs for z in pair}
    while net.count < pairs[-1][-1]:
        z = net.fresh()
        if z not in selected:
            net.add(-z)
    for j, (lo, hi) in enumerate(pairs):
        net.add(lo, hi)
        net.add(-lo, -hi)
        bit = u >> j & 1 if j < d else polarity
        net.add((lo, hi)[bit])
    inputs = [net.fresh() for _ in range(d)]
    predicted = block_product(net, inputs, A, 2)
    count = [-net.one] * len(A).bit_length()
    for j, value in enumerate(predicted):
        carry = -value if y >> j & 1 else value
        updated = []
        for old in count:
            updated.append(xor(net, old, carry))
            carry = net.both(old, carry)
        count = updated
    greater = -net.one
    for j, bit in enumerate(count):
        greater = net.both(greater, bit) if k >> j & 1 else net.either(greater, bit)
    net.add(-greater)
    acc = -net.one
    for pair, val in zip(pairs, inputs):
        acc = xor(net, acc, net.both(pair[1], val))
    net.add(-acc, pairs[-1][1])
    net.add(acc, -pairs[-1][1])
    return padded(net)


def noisy_cubes():
    A = (1, 2, 3, 1, 2)
    count = edges = unique = other = 0
    for y in range(1 << len(A)):
        def within_radius(x):
            return sum(dot(row, x) != (y >> i & 1) for i, row in enumerate(A)) <= 1

        models = [x for x in range(4) if within_radius(x)]
        files = []
        for polarity, u in product(range(2), range(4)):
            raw = noisy_file(A, y, 2, 1, u, polarity)
            files.append(raw)
            assert exact_sat(raw) == any(dot(u, x) == polarity for x in models)
        for a in range(8):
            for j in range(3):
                b = a ^ 1 << j
                if a < b:
                    assert sum((left ^ right).bit_count()
                               for left, right in zip(files[a], files[b])) == 1
                    edges += 1
        unique += len(models) == 1
        other += len(models) != 1
        count += len(files)
    return count, edges, unique, other


def multiple_messages():
    # The first coordinate is forced, the second free. Both sides for its
    # mask are SAT, so the pair race genuinely requires a promise.
    A = (1, 0, 1)
    for u, polarity in product(range(4), range(2)):
        raw = noisy_file(A, 0, 2, 0, u, polarity)
        expected = any(dot(u, x) == polarity for x in (0, 2))
        assert exact_sat(raw) == expected
    return 8


def erasures():
    totals = 0
    d = 3
    for timely in range(1, 1 << (1 << d)):
        masks = [u for u in range(1 << d) if timely >> u & 1]
        for secret in range(1 << d):
            possible = [x for x in range(1 << d) if all(dot(u, x) == dot(u, secret) for u in masks)]
            assert secret in possible and len(possible) * len(masks) <= 1 << d
            totals += 1
    return totals


if __name__ == '__main__':
    print('primal/dual actual files:', primal_dual(), flush=True)
    print('noisy physical cube (files, edges, unique, other):', noisy_cubes(), flush=True)
    print('multiple-message control files:', multiple_messages(), flush=True)
    print('nonempty timely-mask families times secrets:', erasures(), flush=True)
