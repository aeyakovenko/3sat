"""Two remaining instructions when the partial tail is the last initial word read.

The suites preserve the physical words and the verdicts at 24/25 and 29/30 bits.
Widths, addresses and all 24 native value-producing operations are kept exact.
"""

from itertools import combinations, product
import subprocess
import sys

WIDTH = 5
K = 1 << WIDTH
MASK = K - 1
TAIL = (8, 9, 11, 12, 13, 15)
FULL = (9, 11, 13, 16, 19, 21, 24, 27, 31)


def signed(x):
    return x - K if x >= K // 2 else x


def operations(a, b):
    k = b % WIDTH
    return tuple(v & MASK for v in (
        a & b, a | b, a ^ b, a + b, a - b, a * b, a << b, a >> b, signed(a) >> b,
        a << k, a >> k, signed(a) >> k, (a << k) | (a >> (WIDTH-k)),
        (a >> k) | (a << (WIDTH-k)), a == b, a < b, signed(a) < signed(b),
        a != b, a >= b, signed(a) >= signed(b), a // b if b else 0,
        a // b if b else MASK, a % b if b else 0, a % b if b else a,
    ))


TABLES = tuple(tuple(tuple(operations(a,b)[op] for b in range(K))
                     for a in range(K)) for op in range(24))
GUARDS = TABLES[14:17]


def safe(x, width):
    holes = ((1 << width) - 1) ^ x
    return not (holes & (holes >> 1))


def cover(words, bits):
    data = sum(word << (WIDTH*i) for i,word in enumerate(words))
    mask = (1 << bits) - 1
    rotated = ((data << 1) | (data >> (bits-1))) & mask
    return (data | rotated) & mask == mask


def row_mask(booleans):
    return sum(int(value) << i for i,value in enumerate(booleans))


def column(table, a, b):
    return tuple(table[x][y] for x,y in zip(a,b))


def audit_free_full_word():
    rows = list(product(TAIL, FULL))
    tail_good = {11,13,15}
    full_good = {y for y in FULL if safe(y,WIDTH)}
    target = row_mask(x in tail_good and y in full_good for x,y in rows)
    universe = (1 << len(rows)) - 1
    for m in (5,6):
        for j in range(m-1):
            for x,y in rows:
                data = [13]*(m-1) + [x]
                data[j] = y
                assert cover(data,5*m-1) == cover(data,5*m) == (x in tail_good and y in full_good)

    x_col, y_col = zip(*rows)
    raw = (x_col,y_col) + tuple((c,)*len(rows) for c in range(K))
    atomic = {row_mask(column(test,a,b)) for a in raw for b in raw for test in GUARDS}
    atomic |= {universe ^ c for c in atomic}

    def solved(region):
        return any(((cut ^ target) & region) == 0 for cut in atomic)

    assert not any(solved(cut) and solved(universe ^ cut) for cut in atomic)
    results = {column(op,a,b) for op in TABLES for a in raw for b in raw}
    final = {row_mask(column(test,a,b)) for z in results for other in raw
             for a,b in ((z,other),(other,z)) for test in GUARDS}
    final |= {universe ^ c for c in final}
    assert target not in final

    # Loading the address in either raw register can read an arbitrary
    # function of just that axis: all its values are above the six input cells,
    # and the earlier stores are fixed on these rows. Any remaining guard
    # involving the other raw word reduces on an accepting slice to one raw
    # threshold or equality test. A literal load gives a raw word or literal.
    for alphabet,good in ((TAIL,tail_good),(FULL,full_good)):
        for test in GUARDS:
            for c in range(K):
                for cut in ({v for v in alphabet if test[c][v]},
                            {v for v in alphabet if test[v][c]}):
                    assert cut != good and (set(alphabet) - cut) != good
    print(f'{len(rows)} physical pairs in each free-full-word placement, {target.bit_count()} covers. '
          f'{len(atomic)} raw cuts, {len(results)} ALU results, {len(final)} ALU/guard masks.')


def audit_disjoint_pairs():
    # Take both raw operands of each extra instruction equal to its group's
    # letter. A small computed address has to stay pinned; a high result on
    # the original run could never have addressed a mandatory original load.
    letters = (13,7,8)
    for operation in TABLES:
        original = operation[13][13]
        if original < 5:
            assert all(operation[d][d] == original for d in letters)
    for test in GUARDS:
        assert all(test[d][d] == test[13][13] for d in letters)
    rows = list(product([t for t in range(16) if t not in (5,7)],letters,letters))
    labels = [a == b == 13 and x in (11,13,15) for x,a,b in rows]
    target = row_mask(labels)
    universe = (1 << len(rows)) - 1
    x_col,a_col,b_col = zip(*rows)
    registers = {(c,)*len(rows) for c in range(K)} | {x_col,a_col,b_col}
    for op in TABLES:
        for group in (a_col,b_col):
            registers.add(column(op,group,group))
    cuts = {row_mask(column(test,u,v)) for test in GUARDS for u in registers for v in registers}
    cuts |= {universe ^ c for c in cuts}
    def solved(region):
        return any(((c ^ target) & region) == 0 for c in cuts)
    assert not any(solved(c) and solved(universe ^ c) for c in cuts)

    results = {column(op,u,v) for op in TABLES for u in registers for v in registers}
    for positions in combinations(range(4),2):
        # At most one possible store per group, mem[letter]=letter. Both
        # orders agree even when the two writes use the same address.
        memories = []
        for (x,a,b),expected in zip(rows,labels):
            data = [a if j in positions else b for j in range(4)] + [x]
            assert cover(data,24) == cover(data,25) == expected
            memories.append(data + [0]*(K-len(data)))
        for stores_a,stores_b in product((False,True),repeat=2):
            for addr in registers:
                result = []
                for i,cell in enumerate(addr):
                    planted = (stores_a and cell == a_col[i]) or (stores_b and cell == b_col[i])
                    result.append(cell if planted else memories[i][cell])
                results.add(tuple(result))

    order = sorted(range(len(rows)),key=lambda i: not labels[i])
    # Test all guards involving the result. Five bits distinguish equality
    # and both orders and operand orientations; exchanging terminal labels
    # gives their complements. Intersections allow early rejection.
    signatures = [[int(a==b) | (int(a<b)<<1) | (int(a>b)<<2) |
                   (int(signed(a)<signed(b))<<3) | (int(signed(a)>signed(b))<<4)
                   for b in range(K)] for a in range(K)]
    for value in results:
        for peer in registers:
            yes = no = 31
            for i in order:
                signs = signatures[value[i]][peer[i]]
                if labels[i]:
                    yes &= signs
                    no &= ~signs
                else:
                    yes &= ~signs
                    no &= signs
                if not (yes or no):
                    break
            assert not (yes or no)
    assert (len(rows),sum(labels),len(registers),len(cuts),len(results)) == (126,3,45,258,5651)
    print(f'{len(rows)} tail/paired-group rows in each of six placements. '
          f'{len(registers)} granted registers, {len(cuts)} raw cuts, {len(results)} one-step results.')


if __name__ == '__main__':
    if len(sys.argv) == 2:
        output = subprocess.check_output([sys.argv[1],'--dump-operations'],text=True)
        values = [int(x) for x in output.splitlines()[-1].split()]
        assert values == [v for table in TABLES+GUARDS for row in table for v in row]
    audit_free_full_word()
    audit_disjoint_pairs()
