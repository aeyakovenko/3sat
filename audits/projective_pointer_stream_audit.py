"""Check the projective transport, dihedral histories and a reversible escape."""

from itertools import product
from random import Random


def inverse(value, width):
    return pow(value, -1, 1 << width)


def point_index(x, y, width):
    modulus = 1 << width
    if y & 1:
        return x * inverse(y, width) % modulus
    return modulus + (y * inverse(x, width) % modulus) // 2


def point_pair(index, width):
    modulus = 1 << width
    if index < modulus:
        return index, 1
    return 1, 2 * (index - modulus)


def send(matrix, index, width):
    a, b, c, d = matrix
    x, y = point_pair(index, width)
    return point_index(a * x + b * y, c * x + d * y, width)


def multiply(left, right, width):
    a, b, c, d = left
    e, f, g, h = right
    modulus = 1 << width
    return tuple(value % modulus for value in
                 (a * e + b * g, a * f + b * h,
                  c * e + d * g, c * f + d * h))


def upper(t):
    return 1, t, 0, 1


def lower(t):
    return 1, 0, t, 1


def flip(t, width):
    return [upper(t), lower(-inverse(t, width)), upper(t)]


def decompose(matrix, width):
    modulus = 1 << width
    a, b, c, d = matrix
    if not a & 1:
        pivoted = multiply((0, 1, -1, 0), matrix, width)
        return flip(-1, width) + decompose(pivoted, width)
    inv = inverse(a, width)
    return [lower(c * inv % modulus)] + flip(a, width) + flip(-1, width) + [
        upper(inv * b % modulus)
    ]


def orbit_upper(t, index, width):
    modulus = 1 << width
    if index < modulus:
        return (index + t) % modulus
    u = 2 * (index - modulus)
    if u == 0:
        return index
    h = (u & -u).bit_length() - 1
    if 2 * h >= width:
        return index
    inverse_z = inverse(u >> h, width - h)
    residue = inverse_z % (1 << h)
    orbit_coordinate = inverse_z >> h
    shifted = (orbit_coordinate + t) % (1 << (width - 2 * h))
    new_u = inverse(residue + (shifted << h), width - h) << h
    return modulus + new_u // 2


def all_matrices(width):
    modulus = 1 << width
    return (m for m in product(range(modulus), repeat=4)
            if (m[0] * m[3] - m[1] * m[2]) % modulus == 1)


def check_projective():
    rng = Random(7694541)
    count_orbits = count_matrices = count_actions = 0
    for width in range(1, 9):
        modulus = 1 << width
        size = 3 * modulus // 2
        for t in range(modulus):
            for point in range(size):
                assert orbit_upper(t, point, width) == send(upper(t), point, width)
                count_orbits += 1
        if width <= 3:
            matrices = list(all_matrices(width))
        else:
            matrices = []
            for _ in range(200):
                matrix = (1, 0, 0, 1)
                for _ in range(16):
                    form = rng.choice((upper, lower))
                    matrix = multiply(form(rng.randrange(modulus)), matrix, width)
                matrices.append(matrix)
        for matrix in matrices:
            recovered = (1, 0, 0, 1)
            for factor in decompose(matrix, width):
                recovered = multiply(recovered, factor, width)
            assert recovered == matrix
            induced = {send(matrix, point, width) for point in range(size)}
            assert len(induced) == size
            count_matrices += 1
            count_actions += size
    return count_orbits, count_matrices, count_actions


def check_parities():
    rng = Random(72441)
    cases = 0
    for width in range(1, 8):
        modulus = 1 << width
        for _ in range(128):
            bank = [rng.randrange(2) for _ in range(modulus)]
            stream = [(rng.choice((-1, 1)), rng.randrange(modulus))
                      for _ in range(rng.randrange(1 + 2 * modulus))]
            ring = {-1: [0] * modulus, 1: [0] * modulus}
            slope, intercept = 1, 0
            for sign, delta in stream:
                slope, intercept = sign * slope, (sign * intercept + delta) % modulus
                ring[slope][intercept] ^= 1
            for start in range(modulus):
                pos, value = start, 0
                for sign, delta in stream:
                    pos = (sign * pos + delta) % modulus
                    value ^= bank[pos]
                expected = sum(entry * bank[(sign * start + location) % modulus]
                               for sign, histogram in ring.items()
                               for location, entry in enumerate(histogram)) % 2
                assert value == expected
            cases += 1
    return cases


def check_reversible_escape():
    width = 3
    modulus = 1 << width
    size = 3 * modulus // 2
    candidate = list(range(size))
    candidate[0], candidate[modulus // 2] = candidate[modulus // 2], candidate[0]
    checked = 0
    for matrix in product(range(modulus), repeat=4):
        a, b, c, d = matrix
        if (a * d - b * c) % 2 == 0:
            continue
        assert any(send(matrix, index, width) != image
                   for index, image in enumerate(candidate))
        checked += 1
    return checked


if __name__ == "__main__":
    orbit_cases, matrices, actions = check_projective()
    print(f"upper shear orbit cases {orbit_cases}, determinant-one matrices {matrices},"
          f" projective actions {actions}")
    print(f"dihedral histories with every starting address {check_parities()}")
    print(f"width-three invertible matrices rejecting the selective swap {check_reversible_escape()}")
