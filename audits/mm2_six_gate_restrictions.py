"""Verify explicit six-AND circuits on all 510 affine hyperplanes of F2^8.

Input bits 0..3 encode the left 2-by-2 matrix in row-major order. Bits
4..7 encode the right matrix. A gate is a pair of affine masks on these
inputs. Output masks select an affine input form and an XOR of the six gates.
Bit 8 in an affine input mask represents its constant term.
"""

from itertools import product


# Each key is a normal, and its circuit works when that normal has value zero.
CERTIFICATES = {
    1: ([(2, 64), (2, 128), (4, 16), (8, 64), (4, 32), (8, 128)],
        [(0, 1), (0, 2), (0, 12), (0, 48)]),
    6: ([(5, 16), (4, 80), (12, 64), (5, 32), (4, 160), (12, 128)],
        [(0, 3), (0, 24), (0, 6), (0, 48)]),
    17: ([(2, 64), (4, 26), (10, 68), (50, 128), (48, 144), (58, 132)],
         [(16, 1), (16, 24), (0, 7), (0, 42)]),
    18: ([(16, 65), (1, 32), (16, 128), (5, 40), (24, 197), (8, 133)],
         [(0, 1), (0, 6), (0, 53), (0, 42)]),
    22: ([(5, 16), (20, 68), (28, 64), (36, 132), (44, 128), (48, 133)],
         [(4, 3), (4, 41), (4, 6), (4, 24)]),
    102: ([(5, 48), (108, 172), (4, 80), (12, 64), (32, 69), (100, 160)],
          [(64, 21), (32, 48), (0, 12), (12, 42)]),
}


def parity(mask, bits):
    return (mask & bits).bit_count() % 2


def matrix_product(left, right):
    result = 0
    for row in range(2):
        for col in range(2):
            products = [(left >> (2 * row + k)) & (right >> (2 * k + col)) & 1 for k in range(2)]
            result |= (products[0] ^ products[1]) << (2 * row + col)
    return result


def target(x):
    return matrix_product(x & 15, x >> 4)


def transpose(matrix):
    return (matrix & 9) | ((matrix & 2) << 1) | ((matrix & 4) >> 1)


def evaluate(circuit, x):
    gates, outputs = circuit
    assert len(gates) == 6 and len(outputs) == 4
    point = 256 | x
    nonlinear = sum((parity(a, point) & parity(b, point)) << i for i, (a, b) in enumerate(gates))
    return sum((parity(a, point) ^ parity(b, nonlinear)) << j for j, (a, b) in enumerate(outputs))


def pullback(mask, input_images):
    return sum(parity(mask, image) << i for i, image in enumerate(input_images))


def coordinate_changes():
    """Input and inverse output columns for changes of basis and transposition."""
    identity = 9
    inverse = {a: b for a in range(16) for b in range(16)
               if matrix_product(a, b) == identity and matrix_product(b, a) == identity}
    assert len(inverse) == 6
    for left, middle, right in product(inverse, repeat=3):
        for reverse in (False, True):
            # A' = L A M, B' = M^{-1} B R; optionally use (B'^T, A'^T).
            inputs = []
            for bit in range(8):
                x = 1 << bit
                a = matrix_product(matrix_product(left, x & 15), middle)
                b = matrix_product(matrix_product(inverse[middle], x >> 4), right)
                if reverse:
                    a, b = transpose(b), transpose(a)
                inputs.append(a | (b << 4))
            outputs = []
            for bit in range(4):
                c = transpose(1 << bit) if reverse else 1 << bit
                outputs.append(matrix_product(matrix_product(inverse[left], c), inverse[right]))
            yield inputs, outputs


def representative_changes():
    result = {}
    for inputs, outputs in coordinate_changes():
        for representative in CERTIFICATES:
            normal = pullback(representative, inputs)
            if normal in result:
                assert result[normal][0] == representative
            else:
                result[normal] = (representative, inputs, outputs)
    assert set(result) == set(range(1, 256))
    return result


def transport(circuit, inputs, outputs, shift):
    """Compile a concrete six-AND circuit on the translated hyperplane."""
    def affine_mask(mask):
        homogeneous = pullback(mask, inputs)
        return homogeneous | (parity(homogeneous, shift) << 8)

    old_gates, old_outputs = circuit
    gates = [(affine_mask(a), affine_mask(b)) for a, b in old_gates]
    old_outputs = [(affine_mask(a), b) for a, b in old_outputs]
    # target(x) + target(x+shift) is affine by bilinearity. Recover its
    # constant and its eight columns once while constructing the certificate.
    constant = target(shift)
    correction = [target((1 << i) ^ shift) ^ target(1 << i) ^ constant for i in range(8)]
    compiled = []
    for j in range(4):
        affine = pullback(1 << j, correction) | (((constant >> j) & 1) << 8)
        nonlinear = 0
        for i, image in enumerate(outputs):
            if (image >> j) & 1:
                affine ^= old_outputs[i][0]
                nonlinear ^= old_outputs[i][1]
        compiled.append((affine, nonlinear))
    return gates, compiled


def main():
    changes = representative_changes()
    sizes = {normal: 0 for normal in CERTIFICATES}
    cases = 0
    for normal, (representative, inputs, outputs) in changes.items():
        sizes[representative] += 1
        for value in (0, 1):
            shift = (normal & -normal) if value else 0
            circuit = transport(CERTIFICATES[representative], inputs, outputs, shift)
            for x in range(256):
                if parity(normal, x) == value:
                    assert evaluate(circuit, x) == target(x), (normal, value, x)
                    cases += 1
    assert sizes == {1: 18, 6: 12, 17: 54, 18: 27, 22: 108, 102: 36}
    assert cases == 510 * 128
    print(f'Six AND gates verified on every one of the 510 hyperplanes ({cases:,} evaluations).')
    print(f'Homogeneous hyperplane orbit sizes: {sizes}')


if __name__ == '__main__':
    main()
