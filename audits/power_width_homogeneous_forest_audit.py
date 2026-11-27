"""Verify the modular high-byte cycle and the native three-source cases."""
from itertools import product

from homogeneous_ram_word_clock_audit import TAIL, word_pair
from ramsey_dimacs_word_audit import calculate, OPS


U = 255 * int.from_bytes(TAIL, 'little') - 32 * 256**len(TAIL)
V = 255 * 45 + 32
DEN = 255**2


def square_high(byte_width):
    q = (1 + 255 * byte_width) % DEN
    t = (-U**2 * pow(q, -1, DEN)) % DEN
    return (256 * t // DEN + 2 * U * V) % 256


def comparisons(x, y, sign):
    return (x == y, x < y, y < x, (x ^ sign) < (y ^ sign), (y ^ sign) < (x ^ sign))


def main():
    assert U**2 < 256**31
    assert pow(2, 8, 255) == 1
    periods = []
    checks = 0
    for h in range(5, 17):
        width_bytes = 1 << h
        w = width_bytes * 8
        sign = 1 << (w - 1)
        a, b = (int.from_bytes(item, 'little') for item in word_pair(width_bytes))
        predicted = square_high(width_bytes)
        assert (a*a >> (w-8)) % 256 == predicted == square_high(width_bytes << 8)
        assert not 32 <= predicted <= 45
        if h < 13:
            periods.append(predicted)
        # A branch and its complement give identical preservation conditions.
        all_options = [comparisons(v, z, sign) for x,y,z in product((a,b), repeat=3)
                       for v in calculate(x,y,w)]
        for opcode in range(len(OPS)):
            triples = all_options[opcode::len(OPS)]
            for branch in range(len(triples[0])):
                assert any(v[branch] == triples[0][branch] for v in triples[1:])
                checks += 1
    assert periods == [182, 55, 56, 58, 62, 70, 86, 118]
    print(f'{checks} triple-test cases at 12 widths, high-byte cycle {periods}')


if __name__ == '__main__':
    main()
