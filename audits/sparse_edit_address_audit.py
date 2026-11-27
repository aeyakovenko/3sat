"""Check address parity on actual SAT collisions and power sums on all small supports."""

from contextlib import redirect_stdout
from functools import reduce
from io import StringIO
from operator import xor
from pathlib import Path
from tempfile import TemporaryDirectory


def degree(poly):
    return poly.bit_length() - 1


def carryless(a, b):
    product = 0
    while b:
        if b & 1:
            product ^= a
        a <<= 1
        b >>= 1
    return product


def remainder(a, modulus):
    while degree(a) >= degree(modulus):
        a ^= modulus << (degree(a) - degree(modulus))
    return a


def mul(a, b, modulus):
    return remainder(carryless(a, b), modulus)


def table_multiplier(modulus, width):
    s = degree(modulus)
    raw = [[carryless(a, b) for b in range(1 << width)] for a in range(1 << width)]
    chunks = (s + width - 1) // width
    mask = (1 << width) - 1
    reductions = [[remainder(a << (width*i), modulus) for a in range(1 << width)]
                  for i in range(2 * chunks)]
    def multiply(a, b):
        c = 0
        for i in range(chunks):
            for j in range(chunks):
                c ^= raw[(a >> (width*i)) & mask][(b >> (width*j)) & mask] << (width*(i+j))
        return reduce(xor, (row[(c >> (width*i)) & mask] for i, row in enumerate(reductions)), 0)
    return multiply


def small_field_test():
    # Irreducible binary polynomials include X + 1, X² + X + 1, X³ + X + 1, X⁴ + X + 1.
    total = 0
    products = 0
    for modulus in (0b11, 0b111, 0b1011, 0b10011):
        s = degree(modulus)
        n = 1 << s
        for width in range(1, s+1):
            lookup = table_multiplier(modulus, width)
            for a in range(n):
                for b in range(n):
                    assert lookup(a, b) == mul(a, b, modulus)
                    products += 1
        powers = [[1] * n]
        for _ in range(n-1):
            powers.append([mul(a, b, modulus) for a,b in enumerate(powers[-1])])
        for mask in range(1, 1 << n):
            k = mask.bit_count()
            if k % 2 == 0:
                coordinates = [i for i in range(n) if mask & (1 << i)]
                odds = [reduce(xor, (powers[j][i] for i in coordinates), 0) for j in range(1,k,2)]
                assert any(odds)
            total += 1
    print(f'{total:,} nonempty difference masks; {products:,} table field products')


def address_parity(raw, t):
    acc = 0
    for byte_pos, byte in enumerate(raw):
        for j in range(8):
            if ((8*byte_pos+j) >> t) & 1:
                acc ^= (byte >> j) & 1
    return acc


def physical_test():
    # Rebuild, parse, and solve both canonical file pairs using the original construction.
    from switch_index_checksum_audit import stride_pair

    for bound, all_bases in ((48, False), (32, True)):
        with TemporaryDirectory() as stem:
            folder = Path(stem)
            with redirect_stdout(StringIO()):
                stride_pair(bound, all_bases, folder)
            yes = (folder / 'b48-yes.cnf').read_bytes()
            no = (folder / 'b48-no.cnf').read_bytes()
        edits = [8*a+j for a,(left,right) in enumerate(zip(yes,no))
                 for j in range(8) if (left ^ right) & (1 << j)]
        assert len(yes) == len(no) and len(edits) == 2
        difference = edits[1]-edits[0]
        t = (difference & -difference).bit_length()-1
        observed = address_parity(yes,t), address_parity(no,t)
        assert observed[0] != observed[1]
        assert all(((edits[0] >> k) & 1) == ((edits[1] >> k) & 1) for k in range(t))
        print(f'B={bound}: bit addresses {edits}, first separating address bit {t}, SAT/UNSAT parities {observed}')


if __name__ == '__main__':
    small_field_test()
    physical_test()
