"""Check shared enumeration against separate unary deadlines and physical sign edits."""

from itertools import product


def deadline(n, j, r):
    return (2 * (n + j) + 1) << r


def individual(stream, n, j, r):
    data = bytearray(n)
    clock = 0
    index = 0
    for gap, position, value in stream:
        clock += gap
        if clock > deadline(n, j, r):
            break
        if position is None:
            if index == j:
                return bytes(data)
            index += 1
        else:
            data[position] = value
    return None


def first_matching_mark(stream, x, r):
    n = len(x)
    data = bytearray(n)
    differences = sum(byte != 0 for byte in x)
    clock = 0
    index = 0
    for gap, position, value in stream:
        clock += gap
        if clock > deadline(n, n - 1, r):
            break
        if position is None:
            if clock <= deadline(n, index, r) and differences == 0:
                return index
            index += 1
            if index == n:
                break
        else:
            differences -= data[position] != x[position]
            data[position] = value
            differences += value != x[position]
    return None


def check_small_streams():
    n = 2
    actions = [(None, 0), *product(range(n), range(2))]
    events = [(gap, pos, value) for gap in (1, 3) for pos, value in actions]
    inputs = [bytes(bits) for bits in product(range(2), repeat=n)]
    checked = 0
    for length in range(5):
        for stream in product(events, repeat=length):
            for r in (0, 1):
                rows = [individual(stream, n, j, r) for j in range(n)]
                for x in inputs:
                    expected = next((j for j, row in enumerate(rows) if row == x), None)
                    assert first_matching_mark(stream, x, r) == expected
                    checked += 1
    late_then_timely = [(6, None, 0), (1, None, 0)]
    assert individual(late_then_timely, 2, 0, 0) is None
    assert individual(late_then_timely, 2, 1, 0) == bytes(2)
    assert first_matching_mark(late_then_timely, bytes(2), 0) == 1
    return checked


def sign_file(n):
    rows = [b'p cnf 9 22\n']
    for start in (1, 4, 7):
        for bits in product((0, 1), repeat=3):
            if bits == (1, 1, 1):
                continue
            lits = [-(start + i) if bit else start + i for i, bit in enumerate(bits)]
            rows.append((' '.join(map(str, lits)) + ' 0\n').encode())
    prefix = b''.join(rows)
    last = b'-1 -4  7 0\n'
    width = n - len(prefix) - len(last)
    assert width >= 0
    return prefix + last[:-2] + b' ' * width + last[-2:], len(prefix) + 3, len(prefix) + 6


def model_count(data):
    lines = data.splitlines()
    assert lines[0].split() == [b'p', b'cnf', b'9', b'22']
    clauses = [tuple(map(int, line.split())) for line in lines[1:]]
    assert len(clauses) == len(set(clauses)) == 22
    assert all(len(c) == 4 and c[-1] == 0 and len(set(map(abs, c[:3]))) == 3 for c in clauses)
    return sum(all(any(bool(assignment & 1 << (abs(v) - 1)) == (v > 0) for v in c[:3])
                   for c in clauses) for assignment in range(1 << 9))


def check_sign_files():
    for n in (256, 512, 1024, 2048):
        base, positive_slot, negative_slot = sign_file(n)
        assert len(base) == n
        assert base[positive_slot] == ord('-') and base[negative_slot:negative_slot + 2] == b' 7'
        initial = [(1, j, byte) for j, byte in enumerate(base)] + [(1, None, 0)]
        stream = initial + [(1, positive_slot, ord(' ')), (1, None, 0),
                            (1, positive_slot, ord('-')), (1, negative_slot, ord('-')),
                            (1, None, 0)]
        for j, expected in enumerate((1, 1, 0)):
            candidate = individual(stream, n, j, 0)
            assert candidate is not None and model_count(candidate) == expected
            assert first_matching_mark(stream, candidate, 0) == j


if __name__ == '__main__':
    examples = check_small_streams()
    check_sign_files()
    print(f'{examples:,} finite clock comparisons passed; 12 dyadic DIMACS model counts passed.')
