"""Check an explicit bounded-word-palette logspace reduction on proper DIMACS."""

from itertools import product


def source_file(count, clauses):
    header = f'p cnf {count} {len(clauses)}\n'.encode('ascii')
    return header + b''.join((' '.join(map(str, c)) + ' 0\n').encode('ascii') for c in clauses)


def parse(file):
    header, body = file.split(b'\n', 1)
    p, cnf, variables, count = header.split()
    assert (p, cnf) == (b'p', b'cnf')
    tokens = list(map(int, body.split()))
    assert len(tokens) == 4 * int(count) and all(v == 0 for v in tokens[3::4])
    clauses = [tuple(tokens[i:i + 3]) for i in range(0, len(tokens), 4)]
    assert all(len({abs(v) for v in c}) == 3 for c in clauses)
    assert all(0 < abs(v) <= int(variables) for c in clauses for v in c)
    return int(variables), clauses


def reduce_formula(source):
    original_count, clauses = parse(source)
    m = len(source) * 8
    assert original_count <= m  # Restrict to the usual NP-hard source with small identifiers.
    q = (m + 1).bit_length()
    n = 1 << (4 + 2 * q)  # A polynomial target bit length depending only on m.
    width = 16 * (((n + 1).bit_length() + 15) // 16)
    width_bytes = width // 8
    blank = b' ' * width_bytes
    chunks = [b'0' * (width_bytes - 1) + digit for digit in (b'0', b'1')]
    largest = b'1' + chunks[1] * q
    prefix = bytearray(b'p cnf ' + largest + f' {len(clauses)}\n'.encode('ascii'))
    prefix.extend(b' ' * (-len(prefix) % width_bytes))
    for clause in clauses:
        for literal in clause:
            prefix.extend(b' ' * (width_bytes - 2) + (b' 1' if literal > 0 else b'-1'))
            for shift in reversed(range(q)):
                prefix.extend(chunks[(abs(literal) >> shift) & 1])
            prefix.extend(blank)
        prefix.extend(b'0\n'.ljust(width_bytes))
    assert len(prefix) % width_bytes == 0 and len(prefix) < n // 8
    return bytes(prefix), n // 8 - len(prefix), width_bytes, q


def memory_palette(prefix, tail, width_bytes):
    words = {int.from_bytes(prefix[i:i + width_bytes], 'little')
             for i in range(0, len(prefix), width_bytes)}
    # Exactly tail-1 ASCII spaces and a final newline. RAM zero-fills the last
    # word past EOF and every remaining address. Words before the prefix end
    # were already aligned, so this also covers a partial last word.
    whole, rest = divmod(tail - 1, width_bytes)
    if whole:
        words.add(int.from_bytes(b' ' * width_bytes, 'little'))
    words.add(int.from_bytes((b' ' * rest + b'\n').ljust(width_bytes, b'\0'), 'little'))
    words.add(0)
    return words


def assignments(clauses):
    names = sorted({abs(v) for c in clauses for v in c})
    return {bits for bits in product((False, True), repeat=len(names))
            if all(any(bits[names.index(abs(v))] == (v > 0) for v in c) for c in clauses)}


def check(source, semantic):
    _, original = parse(source)
    prefix, tail, width_bytes, q = reduce_formula(source)
    expected_palette = memory_palette(prefix, tail, width_bytes)
    if len(prefix) + tail <= 262144:
        whole = prefix + b' ' * (tail - 1) + b'\n'
        declared, mapped = parse(whole)
        independently_packed = {int.from_bytes(whole[i:i + width_bytes], 'little')
                                for i in range(0, len(whole), width_bytes)} | {0}
        assert independently_packed == expected_palette
    else:
        # All omitted bytes are spaces after the final clause terminator.
        declared, mapped = parse(prefix + b'\n')
    assert len(original) == len(mapped)
    # Decode names without using the writer's bit-shift construction.
    def decode(name):
        digits = str(abs(name))
        assert len(digits) == 1 + q * width_bytes and digits[0] == '1'
        blocks = [digits[i:i + width_bytes] for i in range(1, len(digits), width_bytes)]
        assert all(b[:-1] == '0' * (width_bytes - 1) and b[-1] in '01' for b in blocks)
        value = int(''.join(b[-1] for b in blocks), 2)
        return value if name > 0 else -value

    assert decode(declared) == (1 << q) - 1
    assert [tuple(map(decode, c)) for c in mapped] == original
    if semantic:
        # Common-width decimal renaming preserves increasing numerical order.
        assert assignments(original) == assignments(mapped)
    return len(expected_palette), width_bytes, (len(prefix) + tail) % width_bytes


if __name__ == '__main__':
    possible = list(product((1, -1), (2, -2), (3, -3)))
    for mask in range(1 << len(possible)):
        chosen = [clause for j, clause in enumerate(possible) if (mask >> j) & 1]
        check(source_file(3, chosen), semantic=True)
    print('256 three-variable clause subsets: identical satisfying-assignment sets after parsing')
    for count in (3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095):
        clauses = [(v, -(1 + v % count), 1 + (v + 1) % count) for v in range(1, count + 1)]
        h, width_bytes, tail = check(source_file(count, clauses), semantic=False)
        assert h <= 16
        print(f'{count} identifiers: {h} word values including zero, '
              f'{width_bytes * 8}-bit words, {tail} bytes past the last aligned boundary')
