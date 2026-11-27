"""Finite checks for fixed-length carriers and compact blind-isolation distributions."""

from itertools import combinations, product


def make_carrier(bits):
    width = 1
    while width * (1 << width) < len(bits):
        width += 1
    slots = 1 << width
    padded = bits + (0,) * (slots * width - len(bits))
    base = 10
    while base <= 2 * slots + 3:
        base *= 10
    variables = ((base + slots - 1 + 2) // 3) * 3
    clauses = []
    for start in range(1, variables + 1, 3):
        for assignment in product((0, 1), repeat=3):
            if assignment != (1, 1, 1):
                clauses.append(tuple(-(start + i) if x else start + i for i, x in enumerate(assignment)))
    for i in range(slots):
        chunk = padded[i * width:(i + 1) * width]
        value = sum(bit << j for j, bit in enumerate(chunk))
        clauses.append((2 * i + 1, 2 * i + 2, base + value))
    lines = [f'p cnf {variables} {len(clauses)}']
    lines.extend(' '.join(map(str, clause)) + ' 0' for clause in clauses)
    return ('\n'.join(lines) + '\n').encode()


def decode_and_check_carrier(data):
    lines = data.decode().splitlines()
    _, _, variable_count, clause_count = lines[0].split()
    v, c = int(variable_count), int(clause_count)
    rows = [tuple(map(int, line.split())) for line in lines[1:]]
    assert len(rows) == c == len(set(rows))
    assert all(len(row) == 4 and row[-1] == 0 and len(set(map(abs, row[:3]))) == 3 for row in rows)
    slots = c - 7 * (v // 3)
    width = slots.bit_length() - 1
    assert slots == 1 << width
    base = 10
    while base <= 2 * slots + 3:
        base *= 10
    for i in range(v // 3):
        local = rows[7 * i:7 * i + 7]
        names = tuple(range(3 * i + 1, 3 * i + 4))
        assert all(tuple(map(abs, row[:3])) == names for row in local)
        feasible = [a for a in product((0, 1), repeat=3)
                    if all(any(bool(x) == (lit > 0) for x, lit in zip(a, row[:3])) for row in local)]
        assert feasible == [(1, 1, 1)]
    recovered = []
    for i, (a, b, library, _) in enumerate(rows[-slots:]):
        assert (a, b) == (2 * i + 1, 2 * i + 2)
        value = library - base
        assert 0 <= value < slots
        recovered.extend((value >> j) & 1 for j in range(width))
    return tuple(recovered)


def check_carriers():
    checked = 0
    for length in range(1, 8):
        physical_lengths = set()
        for bits in product((0, 1), repeat=length):
            data = make_carrier(bits)
            physical_lengths.add(len(data))
            recovered = decode_and_check_carrier(data)
            assert recovered[:length] == bits and not any(recovered[length:])
            checked += 1
        assert len(physical_lengths) == 1
    return checked


def field_mul(x, y, modulus, v):
    result = 0
    while y:
        if y & 1:
            result ^= x
        y >>= 1
        x <<= 1
        if x & (1 << v):
            x ^= modulus
    return result


def check_affine_orbits():
    moment_tests = 0
    for v, modulus in ((1, 3), (2, 7), (3, 11)):
        q = 1 << v
        maps = [(a, b) for a in range(1, q) for b in range(q)]
        for t in range(v + 1):
            size = 1 << t
            images = [sum(1 << (field_mul(a, y, modulus, v) ^ b) for y in range(size)) for a, b in maps]
            assert all(w.bit_count() == size for w in images)
            for mask in range(1 << q):
                z = [(w & mask).bit_count() for w in images]
                d = mask.bit_count()
                assert q * sum(z) == len(maps) * d * size
                assert (q * (q - 1) * sum(x * (x - 1) for x in z)
                        == len(maps) * d * (d - 1) * size * (size - 1))
                moment_tests += 1
        for size in range(1, min(3, q) + 1):
            for w in combinations(range(q), size):
                assert size == 1 or any(sum((y >> j) & 1 for y in w) in {1, size - 1} for j in range(v))
    return moment_tests


if __name__ == '__main__':
    print(f'{check_carriers()} unique-model carriers of fixed length by payload width verified.')
    print(f'{check_affine_orbits()} exact filter/distribution first and second moment pairs verified.')
