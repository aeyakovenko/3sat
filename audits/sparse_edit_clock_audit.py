"""Check packed DIMACS, center-preserving gate relations, trees, and matching clocks."""

from itertools import product


def layout(width):
    size = width // 8
    odd = width
    while not odd % 2:
        odd //= 2
    residue = 0
    for digits in range(1, odd + 1):
        residue = (256 * residue + 1) % odd
        if not residue:
            break
    assert not residue and digits <= size // 2
    head = b' 1 2 0\n'.ljust(size - digits - 1) + b'1'
    words = [head + bytes([digit + ord('0')]) * digits for digit in range(3, 8)]
    assert {len(w) for w in words} == {size}
    names = [int(w[-digits-1:]) for w in words]
    values = [int.from_bytes(w, 'little') for w in words]
    center = values[2]
    delta = values[3] - center
    assert [center + d * delta for d in range(-2, 3)] == values
    assert delta % width == (delta * delta) % (1 << width) == 0
    assert values[1] & center == values[1] and values[4] & center == center
    return words, names, values


def check_files(width):
    words, names, _ = layout(width)
    signed_pins = [-1, -2, -names[0], -names[1], names[2], -names[3], -names[4]]
    pins = [(l, 8*s, 9*r) for l in signed_pins for s, r in product((1, -1), repeat=2)]
    count = 0
    for picks in product(range(5), repeat=3):
        prefix = f'p cnf {names[-1]} {len(pins) + 4}\n'.encode()
        prefix += b''.join((' '.join(map(str, c)) + ' 0\n').encode() for c in pins)
        initial = str(names[2]).encode()
        prefix = prefix.ljust(128 * (width // 8) - len(initial)) + initial
        raw = prefix + b''.join(words[j] for j in picks) + b' 1 2 0\n'
        lines = raw.decode('ascii').splitlines()
        header = lines[0].split()
        clauses = [list(map(int, line.split())) for line in lines[1:] if line.strip()]
        assert header == ['p', 'cnf', str(names[-1]), str(len(clauses))]
        assert all(len(c) == 4 and c[-1] == 0 and len({abs(x) for x in c[:3]}) == 3
                   for c in clauses)
        # The four sign choices on the dummy pair impose each signed pin.
        expected = {abs(x): x > 0 for x in signed_pins}
        assert {tuple(c[:3]) for c in clauses[:28]} == set(pins)
        sat = all(any(expected[abs(x)] == (x > 0) for x in c[:3]) for c in clauses[28:])
        assert sat == all(j == 2 for j in picks)
        count += 1
    return count


def relations(width, vals):
    mod = 1 << width
    mask = mod - 1

    def signed(x):
        return x if x < mod // 2 else x - mod

    def rot(x, y):
        s = y % width
        return ((x << s) | (x >> (width - s))) & mask

    ops = [lambda x, y: (x + y) & mask, lambda x, y: (x - y) & mask,
           lambda x, y: (x * y) & mask, rot, lambda x, y: rot(x, -y),
           lambda x, y: x < y, lambda x, y: x == y,
           lambda x, y: signed(x) < signed(y)]
    for clamp in (lambda y: min(y, width), lambda y: y % width):
        ops.extend((lambda x, y, c=clamp: (x << c(y)) & mask,
                    lambda x, y, c=clamp: x >> c(y),
                    lambda x, y, c=clamp: (signed(x) >> c(y)) & mask))
    for table in range(16):
        def gate(x, y, t=table):
            pairs = (~x & ~y, ~x & y, x & ~y, x & y)
            return sum(v & mask for j, v in enumerate(pairs) if t & (1 << j))
        ops.append(gate)
    all_rel = set()
    for op in ops:
        base = op(vals[2], vals[2])
        for rev in (False, True):
            mat = tuple(sum(1 << j for j, y in enumerate(vals)
                            if (op(y, x) if rev else op(x, y)) == base) for x in vals)
            assert mat[2] & 4 and (mat[2] & ~4 or all(mat))
            all_rel.add(mat)
    return all_rel


def tree_closure(rels):
    # A state gives all feasible root values and whether a nontrivial setting
    # exists with the root at center. Every tree is made by joining two roots.
    states = {(31, False)}
    while True:
        extended = set(states)
        for (left, alt_l), (right, alt_r), mat in product(states, states, rels):
            mask = left & sum(1 << j for j in range(5) if mat[j] & right)
            alt = alt_l or alt_r or bool(mat[2] & right & ~4)
            assert alt or mask == 31
            extended.add((mask, alt))
        if extended == states:
            return len(states)
        states = extended


def optimal_program(values, k):
    steps = 0
    start = 0
    while start + k < len(values):
        root = values[start]
        steps += 1
        for val in values[start + 1:start + k + 1]:
            steps += 2
            if val != root:
                return False, steps
        start += k + 1
    for val in values[start:]:
        steps += 2
        if val != 2:
            return False, steps
    return True, steps


def check_programs():
    count = 0
    for m in range(1, 7):
        for k in range(1, m + 1):
            longest = 0
            for v in product(range(5), repeat=m):
                if sum(d != 2 for d in v) <= k:
                    result, steps = optimal_program(v, k)
                    assert result == all(d == 2 for d in v)
                    longest = max(longest, steps)
                    count += 1
            assert longest == 2*m - m // (k + 1)
    return count


if __name__ == '__main__':
    files = 0
    for w in (128, 240, 272, 336, 512, 768, 1024):
        files += check_files(w)
        _, _, values = layout(w)
        rels = relations(w, values)
        print(f'{w}-bit words: {len(rels)} relations, {tree_closure(rels)} tree states')
    print(f'{files} packed proper formula bodies; {check_programs()} sparse-promise executions')
