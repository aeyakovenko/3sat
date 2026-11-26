"""Exhaust local distances in the binary product graph and replay the last read."""
from itertools import combinations, product
from math import perm

from matrix_graph_basis_audit import matmul


def regular(a, b, d):
    # A columns and B rows, independent families of d-bit words.
    columns = [sum(((a >> (i*d+k)) & 1) << i for i in range(d)) for k in range(d)]
    rows = [(b >> (k * d)) & ((1 << d) - 1) for k in range(d)]
    return all(len(set(words)) == d and min(x.bit_count() for x in words) >= 2
               for words in (columns, rows))


def separated(a, b, d, table, neighbors):
    c = table[a][b]
    for da, db, changes in neighbors:
        if changes + (c ^ table[a ^ da][b ^ db]).bit_count() <= 2:
            return False
    return True


def reveal(triple, d, width, seed):
    a, b, c = triple
    length = d * d
    data = a | (b << length) | (c << (2 * length))
    batches = [tuple(range(j, min(j + width, 3*length))) for j in range(0, 3*length, width)]
    reads = []
    seen = 0
    state = seed
    while batches:
        batch = batches.pop(state % len(batches))
        reads.append(batch)
        word = sum(((data >> j) & 1) << k for k, j in enumerate(batch))
        state = 3 * state + word + 1
        seen |= sum(1 << j for j in batch)
        # This partial evaluation is exact: only entries with all their needed inputs read.
        for i in range(d):
            for j in range(d):
                needed = [2*length+i*d+j]
                needed += [i*d+k for k in range(d)]
                needed += [length+k*d+j for k in range(d)]
                if all(seen >> k & 1 for k in needed):
                    expected = sum(((a >> (i*d+k)) & 1) * ((b >> (k*d+j)) & 1)
                                   for k in range(d)) & 1
                    if ((c >> (i*d+j)) & 1) != expected:
                        return False, reads
    return True, reads


def border(a, d, columns, rows, tail):
    extra = len(columns)
    side = d + extra
    out = 0
    for i in range(side):
        for j in range(side):
            if i < d and j < d:
                bit = a >> (i*d + j)
            elif i < d:
                bit = columns[j-d] >> i
            elif j < d:
                bit = rows[i-d] >> j
            else:
                bit = tail >> ((i-d)*extra + j-d)
            out |= (bit & 1) << (i*side+j)
    return out


def check_lifts(a, b, c, d, ab):
    ones = (1 << d) - 1
    for width in (1, 2):
        u = [1] if width == 1 else [ones, ones]
        v = u
        zero = [0]*width
        tail = 1 if width == 1 else 9
        ax = border(a, d, u, zero, tail)
        bx = border(b, d, zero, v, tail)
        cx = border(c ^ int(width == 1), d, u, v, tail)
        expected = border(c ^ ab, d, zero, zero, 0)
        assert matmul(ax, bx, d + width) ^ cx == expected
        if regular(a, b, d):
            assert regular(ax, bx, d + width)


def main():
    for d in (1, 2, 3):
        n = d*d
        count = 1 << n
        tab = [[matmul(a, b, d) for b in range(count)] for a in range(count)]
        flips = [(1 << j, 0) for j in range(n)] + [(0, 1 << j) for j in range(n)]
        neighbors = [(x, y, 1) for x, y in flips]
        neighbors.extend((a ^ c, b ^ e, 2) for (a,b), (c,e) in combinations(flips, 2))
        centers = []
        for a in range(count):
            for b in range(count):
                good = regular(a, b, d)
                assert separated(a, b, d, tab, neighbors) == good
                if good:
                    centers.append((a, b, tab[a][b]))
        assert len(centers) == perm((1 << d) - d - 1, d)**2
        for u, v in product(range(1 << d), repeat=2):
            preserved = all(not ((u >> i & 1) and (v >> j & 1))
                            for i in range(d) for j in range(d))
            if preserved:
                assert min(u.bit_count() + 1, v.bit_count() + 1) <= 1
        if d <= 2:
            for a, b in product(range(count), repeat=2):
                for c in range(count):
                    check_lifts(a, b, c, d, tab[a][b])
        for width, seed in ((1, 1), (4, 5)):
            images = set()
            for triple in centers:
                on_graph, reads = reveal(triple, d, width, seed)
                assert on_graph and sum(map(len, reads)) == 3*n
                partner = list(triple)
                flip = reads[-1][0]
                partner[flip // n] ^= 1 << (flip % n)
                partner = tuple(partner)
                assert partner not in images
                images.add(partner)
                off_graph, new_reads = reveal(partner, d, width, seed)
                assert not off_graph and new_reads == reads
                check_lifts(*triple, d, triple[2])
                check_lifts(*partner, d, tab[partner[0]][partner[1]])
                a, b, c = partner
                error = tab[a][b] ^ c
                rows = {(error >> (i*d)) & ((1 << d)-1) for i in range(d)} - {0}
                assert len(rows) == 1  # nonzero rank one over F2
        print(f'd={d}: checked all {count**2} centers; {len(centers)} isolated; two adaptive schedules')


if __name__ == '__main__':
    main()
