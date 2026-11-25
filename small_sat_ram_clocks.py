"""Exact native clocks on ordered 16-bit clauses over one fixed triple."""
from collections import defaultdict
from functools import cache
from itertools import product

HEADER = 0x3C1F
BASE = (1 << 11) | (2 << 7) | (3 << 3)

# N is the encoded bit length. Words contain 16 bits in the tested range.
# The prefix checks the header, alignment, and every clause name.
PREFIX = [
    ('gt', 'N', 65520, 'other'), ('and', 'r', 'N', 15),
    ('ne', 'r', 0, 'other'), ('load', 'r', 0), ('ne', 'r', HEADER, 'other'),
    ('shr', 'end', 'N', 4), ('mov', 'i', 1),
]
SCAN = [
    'scan', ('eq', 'i', 'end', 'ready'), ('load', 'rec', 'i'),
    ('shr', 'r', 'rec', 3), ('ne', 'r', BASE >> 3, 'other'),
]
NEXT = [('add', 'i', 'i', 1), ('jump', 'scan'), 'ready']
RESCAN = [
    ('le', 'end', 8, 'sat'), ('mov', 'p', 0), 'trial', ('mov', 'i', 1),
    'seek', ('eq', 'i', 'end', 'sat'), ('load', 'rec', 'i'),
    ('and', 'r', 'rec', 7), ('eq', 'r', 'p', 'found'),
    ('add', 'i', 'i', 1), ('jump', 'seek'),
    'found', ('add', 'p', 'p', 1), ('ne', 'p', 8, 'trial'),
    ('halt', 0), 'sat', ('halt', 1)
]
MARK = [
    ('and', 'p', 'rec', 7), ('shl', 'bit', 1, 'p'),
    ('or', 'seen', 'seen', 'bit'),
]
PROGRAMS = (
    PREFIX + SCAN + NEXT + RESCAN,
    PREFIX + [('mov', 'seen', 0)] + SCAN + MARK + NEXT +
    [('eq', 'seen', 255, 'unsat'), ('halt', 1), 'unsat', ('halt', 0)],
)


def assemble(source):
    pc = 0
    labels = {}
    code = []
    for line in source:
        if isinstance(line, str):
            labels[line] = pc
        else:
            code.append(line)
            pc += 1
    return code, labels


ASSEMBLED = [assemble(source) for source in PROGRAMS]


def run(program, signs):
    code, labels = ASSEMBLED[program]
    data = [HEADER] + [BASE | s for s in signs]
    reg = {'N': 16 * len(data)}
    pc = clock = 0

    def read(x):
        return x if isinstance(x, int) else reg[x]

    while True:
        op, *a = code[pc]
        pc += 1
        clock += 1
        if op == 'halt':
            return a[0], clock
        if op == 'load':
            reg[a[0]] = data[read(a[1])]
        elif op == 'mov':
            reg[a[0]] = read(a[1])
        elif op == 'jump':
            pc = labels[a[0]]
        elif op in ('eq', 'ne', 'gt', 'le'):
            x, y = read(a[0]), read(a[1])
            if {'eq': x == y, 'ne': x != y, 'gt': x > y, 'le': x <= y}[op]:
                pc = labels[a[2]]
        else:
            x, y = read(a[1]), read(a[2])
            reg[a[0]] = {'add': lambda: x + y, 'and': lambda: x & y,
                         'or': lambda: x | y, 'shr': lambda: x >> y,
                         'shl': lambda: x << y}[op]() & 65535


def clock(signs):
    m = len(signs)
    t = 7 + (6 * m + 1) + 1
    if m < 8:
        return t + 1
    t += 1  # initialize p
    for p in range(8):
        t += 1  # initialize i
        if p not in signs:
            return t + 6 * m + 1 + 1
        t += 6 * signs.index(p) + 4 + 2
    return t + 1


def exhaustive(m):
    """Exact max clock and multiplicity, partitioning sequences by first missing sign."""
    if m < 8:
        return clock([0] * m), 8 ** m, [0] * m
    best = 0
    count = 0
    witness = []
    for missing in range(9):
        # Each previously unseen present sign below 'missing' adds 6*first_position.
        # All other differences in running time depend only on m and 'missing'.
        required = (1 << missing) - 1

        @cache
        def extend(i, used):
            if i == m:
                return (0, 1, ()) if used == required else (-1, 0, ())
            best_rest, ways, example = -1, 0, ()
            for p in range(8):
                if p == missing:
                    continue
                bit = (1 << p) & required
                cost, number, suffix = extend(i + 1, used | bit)
                if not number:
                    continue
                value = cost + (6 * i if bit and not used & bit else 0)
                if value > best_rest:
                    best_rest, ways, example = value, 0, (p,) + suffix
                if value == best_rest:
                    ways += number
            return best_rest, ways, example

        _, ways, example = extend(0, 0)
        if not ways:
            continue
        total = clock(example)
        if total > best:
            best, count, witness = total, 0, list(example)
        if total == best:
            count += ways
    return best, count, witness


def check():
    for m in range(5):
        for signs in product(range(8), repeat=m):
            expect = int(len(set(signs)) < 8)
            assert run(0, signs) == (expect, clock(signs))
            assert run(1, signs) == (expect, 11 + 9 * m)
    print('clauses bits rescan-max maximizers bitmap example')
    for m in [*range(13), 16, 24, 32]:
        worst, ways, signs = exhaustive(m)
        assert run(0, signs) == (int(len(set(signs)) < 8), worst)
        assert run(1, signs) == (int(len(set(signs)) < 8), 11 + 9 * m)
        if 0 < m < 8:
            assert worst <= 16 * (m + 1)
        print(m, 16 * (m + 1), worst, ways, 11 + 9 * m, ''.join(map(str, signs)))
    from itertools import permutations
    # Direct clock tests on independent labeled permutations and repeated patterns.
    for signs in permutations(range(8)):
        assert clock(signs) == clock(tuple(range(8)))
    assert exhaustive(8)[0] > 144


if __name__ == '__main__':
    check()
