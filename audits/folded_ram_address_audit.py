"""Check byte-run generators, alias preservation and folded movement at actual word sizes."""
from itertools import product
from random import Random


def encode(width, bits, count, target, rng):
    def digits(i):
        return ''.join('0' * (width - 1) + v for v in f'{i:0{bits}b}')
    def literal(i, positive):
        return ' ' * (width - 2) + (' ' if positive else '-') + '1' + digits(i)
    header = f'p cnf 1{digits(2**bits-1)} {count}\n'
    header += ' ' * (-len(header) % width)
    data = header + ''.join(
        ''.join(literal(rng.randrange(1, 2**bits), rng.getrandbits(1)) for _ in range(3))
        + ' 0\n' + ' ' * (width - 3) for _ in range(count))
    assert len(data) < target
    return (data + ' ' * (target - len(data) - 1) + '\n').encode('ascii')


def coordinate(address, cuts):
    scaled = 255 * address % (1 << cuts[-1])
    digits, locations, signs = [], [], []
    for start, stop in zip(cuts, cuts[1:]):
        radix = 1 << (stop - start)
        val = (scaled >> start) % radix
        fd = min(val, radix-val)
        digits.append(val)
        locations.append(fd)
        signs.append(fd != val)
    return tuple(locations), tuple(signs)


def inverse(locations, signs, cuts):
    scaled = 0
    for f, negative, start, end in zip(locations, signs, cuts, cuts[1:]):
        digit = (1 << (end-start))-f if negative else f
        scaled |= digit << start
    return scaled * pow(255, -1, 1 << cuts[-1]) % (1 << cuts[-1])


def cuts_and_generators(words):
    width = len(next(iter(words)))
    cuts = {0, 8 * width}
    coeff = {}
    for word in words:
        last = 0
        total = 0
        for i, val in enumerate(word):
            if val != last:
                cuts.add(8*i)
                total += (last-val) << (8*i)
                last = val
        number = int.from_bytes(word, 'little')
        assert total + (last << (width*8)) == 255 * number
        coeff[number] = 255
    return cuts, coeff


def main():
    rng = Random(661105)
    for w in range(2, 11):
        for sub in range(1 << (w-1)):
            cuts = [0] + [i for i in range(1,w) if sub >> (i-1) & 1] + [w]
            for y in range(1 << w):
                assert inverse(*coordinate(y, cuts), cuts) == y
    moves = 0
    for n_bits, coefficient, count in product((19, 20, 22), (1, 2, 3), (10, 100)):
        width_bits = (((1 << n_bits) + 2)**coefficient - 1).bit_length()
        width = 2 * ((width_bits + 15) // 16)
        target = 1 << (n_bits-3)
        a = encode(width, 7, count, target, rng)
        b = encode(width, 7, count, target, rng)
        words = {bytes(width)}
        for data in (a,b):
            words.update(data[i:i+width].ljust(width, b'\0') for i in range(0,len(data),width))
        cut_set, generators = cuts_and_generators(words)
        cut_set.add(n_bits)
        if n_bits == width*8:
            continue
        cuts = sorted(cut_set)
        q = 1 << cuts[-1]
        literal = -7
        generators[literal % q] = 255 * abs(literal)
        generators[1 << n_bits] = 255
        generators[cuts[-1]] = 255*cuts[-1]
        for value, amplitude in generators.items():
            for _ in range(50):
                y = rng.randrange(q)
                before = coordinate(y, cuts)[0]
                for new in ((y+value)%q,(y-value)%q,(value-y)%q):
                    after = coordinate(new, cuts)[0]
                    assert all(abs(v-u) <= 2*amplitude+2 for v,u in zip(before,after))
                    moves += 1
    print(f'All folds through 10 bits invert correctly; {moves} affine updates passed the tape-motion bound')


if __name__ == '__main__':
    main()
