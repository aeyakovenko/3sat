"""One native program, actual clocks, and exact joint distributions on its positive files."""

from collections import Counter
from itertools import combinations, product
from math import comb
from random import Random

# ALUs and LOADs have their next fixed label as the last field. Comparisons
# carry both fixed successors. A string operand denotes a data register.
BATCH = (
    ("load", "count", 0, 1),
    ("mul", "end", "count", 4, 2),
    ("add", "end", "end", 1, 3),
    ("add", "base", 0, 1, 4),
    ("eq", "base", "end", "yes", 5),
    ("add", "qa", "base", 1, 6),
    ("load", "q", "qa", 7),
    ("add", "ma", "base", 2, 8),
    ("load", "m", "ma", 9),
    ("add", "na", "base", 3, 10),
    ("load", "n", "na", 11),
    ("and", "j", "q", "n", 12),
    ("lt", "j", 4, 13, "no"),
    ("add", "addr", "base", "j", 14),
    ("load", "x", "addr", 15),
    ("eq", "m", 11, 16, 17),
    ("eq", "x", 4, 23, 17),
    ("load", "p", "base", 18),
    ("and", "g", "p", "m", 19),
    ("eq", "g", 0, 20, "no"),
    ("eq", "j", 0, 21, "no"),
    ("eq", "m", 15, 22, 23),
    ("eq", "n", 15, "no", 23),
    ("add", "base", "base", 4, 4),
)

GUEST = (
    ("load", "q", 1, 1),
    ("load", "m", 2, 2),
    ("load", "n", 3, 3),
    ("and", "j", "q", "n", 4),
    ("load", "x", "j", 5),
    ("eq", "m", 11, 6, 7),
    ("eq", "x", 4, "yes", 7),
    ("load", "m", 2, 8),
    ("eq", "m", 15, 16, 9),
    ("load", "p", 0, 10),
    ("and", "h", "p", "m", 11),
    ("eq", "h", 0, 12, "no"),
    ("load", "q", 1, 13),
    ("load", "n", 3, 14),
    ("and", "h", "q", "n", 15),
    ("eq", "h", 0, "yes", "no"),
    ("load", "n", 3, 17),
    ("eq", "n", 15, "no", 18),
    ("load", "p", 0, 19),
    ("eq", "p", 0, 20, "no"),
    ("load", "q", 1, 21),
    ("and", "h", "q", "n", 22),
    ("eq", "h", 0, "yes", "no"),
)


def run(code, memory, w):
    mask = (1 << w) - 1
    reg = {}
    pc = clock = 0

    def val(x):
        return reg.get(x, 0) if isinstance(x, str) else x

    while isinstance(pc, int):
        op, a, b, *rest = code[pc]
        clock += 1
        if op == "load":
            addr = val(b)
            reg[a] = memory[addr] if addr < len(memory) else 0
            pc = rest[0]
        elif op in ("eq", "lt"):
            test = val(a) == val(b) if op == "eq" else val(a) < val(b)
            pc = rest[0] if test else rest[1]
        else:
            arg, pc = rest
            lhs, rhs = val(b), val(arg)
            if op == "add":
                z = lhs + rhs
            elif op == "mul":
                z = lhs * rhs
            else:
                assert op == "and"
                z = lhs & rhs
            reg[a] = z & mask
    return pc == "yes", clock


def target(label, qlabel):
    # The top pair in each target nibble is 01 or 10.
    p = 4 + label
    q = 4 + qlabel
    return p, q, 15-p, 15-q


def expected(p,q,m,n):
    return (p & m) == (q & n) == 0 and (m,n) != (15,15)


def physical():
    for data in product(range(16), repeat=4):
        fine = expected(*data)
        assert run(GUEST, data, 4)[0] == fine
        assert run(BATCH, (1, *data), 4)[0] == fine
    singleton = Counter()
    for p,q in product(range(8), repeat=2):
        data = target(p,q)
        singleton[run(GUEST, data, 4)] += 1
        assert run(BATCH, (1,*data), 4) == (True, 19 + 4*(p != 0))
    assert singleton == {(True,7):8, (True,15):56}

    rng = Random(16397)
    trials = 0
    for variables in range(3, 9):
        for size in (1, 3, 8, 17, 65):
            clauses = [(rng.sample(range(variables),3),rng.randrange(8)) for _ in range(size)]
            qlabels = [rng.randrange(8) for _ in clauses]
            for row in range(1 << variables):
                words = [size]
                true = 0
                for (indices, flips), q in zip(clauses, qlabels):
                    pattern = sum(((row >> i) & 1) << j for j,i in enumerate(indices)) ^ flips
                    true += pattern != 0
                    words.extend(target(pattern, q))
                w = max(4, (4*size+1).bit_length())
                assert run(BATCH, words, w) == (True, 5 + 14*size + 4*true)
                trials += 1
    return trials


def no_all_late(m, t):
    s = t + 1
    assert 7*s <= m
    mass = [comb(m,j) * 7**(m-j) for j in range(m+1)]
    atom = mass[0]
    for j in range(s+1):
        mass[j] += ((-1)**(j+1) if j else -1) * comb(s,j) * atom
    return mass


def verify_moments(mass, m, t):
    den = 8**m
    assert min(mass) >= 0 and sum(mass) == den
    for d in range(t+1):
        assert sum(w*comb(j,d) for j,w in enumerate(mass) if j >= d) * 8**d == den*comb(m,d)


def finite_difference():
    tested = 0
    for m in range(14, 113):
        for t in range(1, min(m//7-1, 8)+1):
            mass = no_all_late(m, t)
            assert mass[0] == 0
            verify_moments(mass, m, t)
            tested += 1
    return tested


def gf512_mul(a,b):
    value = 0
    while b:
        if b & 1:
            value ^= a
        b >>= 1
        a <<= 1
        if a & 512:
            a ^= (1 << 9) | (1 << 4) | 1
    return value


def binary_rank(vectors):
    pivots = {}
    for v in vectors:
        while v:
            i = v.bit_length()-1
            if i not in pivots:
                pivots[i] = v
                break
            v ^= pivots[i]
    return len(pivots)


def trace_wiring():
    m = 512
    mul = [[gf512_mul(a,b) for b in range(m)] for a in range(m)]
    def power(a,n):
        out = 1
        while n:
            if n & 1:
                out = mul[out][a]
            a = mul[a][a]
            n >>= 1
        return out
    assert all(power(a, 511) == 1 for a in range(1,m))
    sub = [a for a in range(m) if power(a,8) == a]
    assert len(sub) == 8
    # Use an F2-linear indexing of the subfield, so that the input-bit wiring is affine.
    h = next(a for a in sub if a not in (0,1))
    basis = (1,h,mul[h][h])
    label = {}
    for z in range(8):
        out = 0
        for j, b in enumerate(basis):
            if z >> j & 1:
                out ^= b
        label[out] = z
    assert set(label) == set(sub) and label[0] == 0
    tr = [label[a ^ power(a,8) ^ power(a,64)] for a in range(m)]
    cube = [power(a,3) for a in range(m)]
    rng = Random(837137)
    for _ in range(96):
        a, b, c = rng.randrange(m), rng.randrange(m), rng.randrange(m)
        values = [tr[cube[t]^a^mul[t][b^mul[t][c]]] for t in range(m)]
        f = values.count(0)
        assert (8*f-m)**2 <= 49*4*m
        assert f and f != m
        words = [m]
        for v in values:
            words.extend(target(v, rng.randrange(8)))
        assert run(BATCH, words, 12) == (True, 5+14*m+4*(m-f))
    for _ in range(128):
        points = rng.sample(range(m),3)
        columns = []
        for i in range(27):
            b, j = divmod(i,9)
            columns.append(sum(tr[mul[1 << j][power(t,b)]] << (3*l) for l,t in enumerate(points)))
        assert binary_rank(columns) == 9
    return "96 complete length-512 native affine clocks and 128 exact three-site rank tests"


def projective_pair():
    def mul8(a,b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            b >>= 1
            a <<= 1
            if a & 8:
                a ^= 11
        return r
    lines = [tuple(a ^ mul8(t,b) for t in range(8)) + (b,)
             for a,b in product(range(8), repeat=2)]
    assert len(set(lines)) == 64
    assert Counter(line.count(0) for line in lines) == {1:63,9:1}
    for i,j in combinations(range(9),2):
        assert len({(line[i],line[j]) for line in lines}) == 64
    for site,bit in product(range(9),range(3)):
        inputs = [i for i in range(6) if (lines[1 << i][site] >> bit) & 1]
        assert len(inputs) <= 4
        for seed, line in enumerate(lines):
            assert (sum((seed >> i) & 1 for i in inputs) % 2) == ((line[site] >> bit) & 1)
    count = 0
    for p,q in product(lines,repeat=2):
        words = [9]
        for a,b in zip(p,q):
            words.extend(target(a,b))
        assert run(BATCH, words, 6) == (True, 5+14*9+4*(9-p.count(0)))
        count += 1
    return count


def main():
    print(f"65,536 catalogs for each program; {physical():,} assignment-dependent uninterrupted clocks")
    print(f"{projective_pair():,} nine-record projective clocks; every pair of records is independent")
    print(trace_wiring())
    print(f"{finite_difference()} exact binomial moment systems with zero all-late mass")


if __name__ == "__main__":
    main()
