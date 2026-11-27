"""Check the cyclic-overlap proof, sparse images, and modular physical identity."""
from itertools import product


def rotate(x, count, width):
    count %= width
    return ((x << count) | (x >> (width - count))) & ((1 << width) - 1)


def geometry(width, ell, count):
    limit = 1 << ell
    right, left, logical = set(), set(), set()
    overlap = set()
    for x in range(1 << width):
        p, q, s = rotate(x, count, width), rotate(x, -count, width), x >> count
        if max(p, q) < limit:
            overlap.add(p)
            overlap.add(q)
        if count >= width - ell:
            logical.add(s)
        elif q < limit:
            assert q == s
        if count < width - ell and max(p, s) < limit:
            if count < ell or 2 * count <= width:
                left.add(p)
            else:
                right.add(s)
    twice = (2 * count) % width
    fixed = min(ell, width - ell, twice, width - twice)
    assert len(overlap) <= 2 * (1 << (ell - fixed))
    if count >= width - ell:
        assert len(logical) <= 1 << (width - count)
    elif count < ell:
        assert len(left) <= 1 << (ell - min(count, width - ell - count))
    elif 2 * count <= width:
        assert len(left) <= 1 << (ell - min(ell, width - 2 * count))
    else:
        assert len(right) <= 1 << max(0, ell - (2 * count - width))
    sparse = overlap | logical | left | right
    for x in range(1 << width):
        results = {x >> count, rotate(x, count, width), rotate(x, -count, width)}
        assert sum(t < limit and t not in sparse for t in results) <= 1


def affine_overlap(width, ell, count):
    # Arbitrary fixed high patterns and the target pattern of all zeroes.
    blocks = [0] * (1 << (width - ell))
    for x in range(1 << width):
        if rotate(x, count, width) < 1 << ell:
            blocks[x >> ell] += 1
    extra = min(ell, width - ell, count, width - count)
    assert max(blocks) <= 1 << (ell - extra)


def physical_products():
    denominator = 255 * 256
    probes = 0
    for width, digit in product((248, 256, 512, 1016, 1024, 2048, 4096, 8200, 32768), '6789'):
        width_bytes = width // 8
        # Increase the byte offset at large widths, independently of residue choice.
        k = 1
        while 256**(k + 1) <= width // 128:
            k += 1
        text = f'{digit} 1 0\n'.encode()
        raw = bytearray(b' ' * width_bytes)
        raw[k:k + len(text)] = text
        raw[-1] = ord('4')
        a = int.from_bytes(raw, 'little')
        diff = int.from_bytes(text, 'little') - int.from_bytes(b' ' * len(text), 'little')
        e = denominator * 256**k * diff - 8192
        u = 1 << width
        assert e and denominator * a == (52 * 255 + 32) * u + e
        for y in (0, 1, 2, a, a - 1, u - a, u - 1, u // width):
            assert denominator * ((a * y) % u) % u == e * y % u
            probes += 1
    return probes


def main():
    shapes = 0
    for width in range(3, 13):
        for ell in range(1, width):
            for r in range(1, width):
                geometry(width, ell, r)
                affine_overlap(width, ell, r)
                shapes += 1
    probes = physical_products()
    print(f'{shapes} widths/sizes/rotations exhausted, {probes} exact physical modular products')


if __name__ == '__main__':
    main()
