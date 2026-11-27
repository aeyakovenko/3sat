"""Finite audit of the late-word wrapper on the journal's actual ASCII files.

Requires pycosat, as does the projection generator imported below.
"""
from itertools import product
from random import Random

from compact_product_projection_audit import ProductLayout, check_models, product_bits


class WordPatch:
    def __init__(self, d, r, chunk, width):
        self.layout = ProductLayout(d, chunk)
        self.d = d
        self.width = width
        self.area = d * d
        self.nbits = 3 * self.area
        zeros = [0] * self.nbits
        self.base = self.layout.serialize(zeros)
        self.positions = []
        data_by_word = {}
        for k in range(self.nbits):
            zeros[k] = 1
            changed = self.layout.serialize(zeros)
            zeros[k] = 0
            pos, = (i for i, v in enumerate(changed) if self.base[i] != v)
            assert changed[pos] ^ self.base[pos] == 1
            self.positions.append(pos)
            data_by_word.setdefault(pos // width, []).append(k)
        selected = {2 * self.area + i * d + j for i in range(r) for j in range(r)}
        self.pending = {word: keys for word, keys in data_by_word.items()
                        if all(k in selected for k in keys)}
        self.hidden = {k for keys in self.pending.values() for k in keys}
        assert self.hidden
        self.mask = {}
        for word, keys in data_by_word.items():
            self.mask[word] = sum(1 << (8 * (self.positions[k] % width)) for k in keys)

    def encode(self, data):
        result = bytearray(self.base)
        for bit, pos in zip(data, self.positions):
            result[pos] |= bit
        return result

    def word(self, buf, index):
        begin = index * self.width
        return int.from_bytes(buf[begin:begin + self.width], 'little')

    def split(self, raw):
        """Return None for fallback. Only the terminal loop reads pending words."""
        scratch = bytearray(self.base)
        # All fixed positions outside pending words are checked byte for byte.
        for start in range(0, len(raw), self.width):
            word = start // self.width
            if word in self.pending:
                continue
            got = self.word(raw, word)
            if (got ^ self.word(self.base, word)) & ~self.mask.get(word, 0):
                return None
            scratch[start:start + self.width] = raw[start:start + self.width]
        values = [scratch[p] & 1 for p in self.positions]
        expected = product_bits(values[:self.area], values[self.area:2*self.area], self.d)
        for k in self.hidden:
            values[k] = expected[k - 2*self.area]
            scratch[self.positions[k]] |= values[k]
        guest = expected != values[2*self.area:]
        assert scratch == self.layout.serialize(values)
        invalid = mismatch = False
        for word in sorted(self.pending):
            difference = self.word(raw, word) ^ self.word(scratch, word)
            invalid |= bool(difference & ~self.mask[word])
            mismatch |= bool(difference & self.mask[word])
        return None if invalid else guest or mismatch


def check_operand(d, r, a, b, c):
    """Brute-force the pivot solve; independently check the forced completion."""
    k0 = list(range(r))
    possible_rows = list(product((0, 1), repeat=r))
    for start in range(0, d - r + 1, r):
        cols = range(start, start + r)
        images = {tuple(sum(row[k] * b[k*d+j] for k in k0) % 2 for j in cols): row
                  for row in possible_rows}
        if len(images) != len(possible_rows):
            continue
        patched = a.copy()
        for i in range(r):
            rhs = tuple(c[i*d+j] ^ (sum(a[i*d+k] * b[k*d+j] for k in range(r, d)) % 2)
                        for j in cols)
            patched[i*d:i*d+r] = images[rhs]
        assert (product_bits(a, b, d) != c) == (
            patched != a or product_bits(patched, b, d) != c)
        return True
    return False


def main():
    rng = Random(221031)
    verdicts = operand = counted_models = 0
    for d, r, chunk, width, exhaustive in [(2, 1, 1, 2, True), (4, 2, 2, 8, False)]:
        patch = WordPatch(d, r, chunk, width)
        n = patch.area
        trials = (product((0, 1), repeat=3*n) if exhaustive else
                  ([rng.randrange(2) for _ in range(3*n)] for _ in range(200)))
        for case in trials:
            a, b, c = list(case[:n]), list(case[n:2*n]), list(case[2*n:])
            expected = product_bits(a, b, d)
            buf = patch.encode(case)
            assert patch.split(buf) == (expected != c)
            operand += check_operand(d, r, a, b, c)
            verdicts += 1
        last = patch.pending[max(patch.pending)][-1]
        for _ in range(4):
            a, b = ([rng.randrange(2) for _ in range(n)] for _ in range(2))
            exact = a + b + product_bits(a, b, d)
            partner = exact.copy()
            partner[last] ^= 1
            assert check_models(patch.layout, exact) == 0
            assert check_models(patch.layout, partner) == 1
            counted_models += 2
            for which in [exact, partner]:
                buf = patch.encode(which)
                assert patch.split(buf) == (which == partner)
                buf[patch.positions[last]] ^= 2
                assert patch.split(buf) is None
        print(f'd={d}, hidden source bits={len(patch.hidden)}, pending words={len(patch.pending)}')
    print(f'{verdicts} verdicts, {operand} invertible operand cases, '
          f'{counted_models} SAT model counts on paired files')


if __name__ == '__main__':
    main()
