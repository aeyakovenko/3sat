"""Exhaust independent projective wire bases over F_2 and F_3 for COPY and OR."""

from collections import Counter
from itertools import permutations, product


def normalize(vector, prime):
    first = next(x for x in vector if x)
    inverse = pow(first, -1, prime)
    return tuple(x * inverse % prime for x in vector)


def projective_bases(prime):
    return sorted({
        normalize((a, b, c, d), prime)
        for a, b, c, d in product(range(prime), repeat=4)
        if (a * d - b * c) % prime
    })


def inverse_transpose(matrix, prime):
    a, b, c, d = matrix
    return normalize((d, -c % prime, -b % prime, a), prime)


def change_port(vector, port, matrix, prime):
    a, b, c, d = matrix
    result = list(vector)
    mask = 1 << port
    for low in range(len(vector)):
        if not low & mask:
            high = low | mask
            x, y = vector[low], vector[high]
            result[low] = (a * x + b * y) % prime
            result[high] = (c * x + d * y) % prime
    return normalize(result, prime)


def parity(vector):
    parities = {index.bit_count() % 2 for index, value in enumerate(vector) if value}
    return next(iter(parities)) if len(parities) == 1 else None


def shared_bases(vector, bases, prime):
    """Keep possibilities on port zero, with both other bases freely chosen."""
    others = {
        change_port(change_port(vector, 1, a, prime), 2, b, prime)
        for a, b in product(bases, repeat=2)
    }
    return {
        shared for shared in bases
        if any(parity(change_port(t, 0, shared, prime)) is not None for t in others)
    }


def merged_orbit(vector, bases, prime):
    counts = Counter({vector: 1})
    for port in range(4):
        updated = Counter()
        for tensor, count in counts.items():
            for basis in bases:
                updated[change_port(tensor, port, basis, prime)] += count
        counts = updated
    return counts


def passes_four_port_identity(vector, order, parity_bit, prime):
    """The four-term matchgate identity, for either parity and any ordering."""
    x, y, z, t = (1 << port for port in order)
    offset = x if parity_bit else 0

    def complement_product(mask):
        index = offset ^ mask
        return vector[index] * vector[index ^ 15]

    return (complement_product(0) - complement_product(x | y)
            + complement_product(x | z) - complement_product(x | t)) % prime == 0


def complementary_sum(vector):
    return sum(vector[i] * vector[i ^ 15] for i in range(8)) % 2


def check_degeneration(prime):
    hadamard = (1, 1, 1, prime - 1)
    for t in range(1, prime):
        inverse = pow(t, -1, prime)
        vector = tuple({0: 1, 3: 1, 12: -1, 15: -(t ** 2)}.get(i, 0) % prime
                       for i in range(16))
        vector = change_port(vector, 0, (1, 0, 0, -inverse % prime), prime)
        vector = change_port(vector, 2, (1, 0, 0, inverse), prime)
        for port in range(4):
            vector = change_port(vector, port, hadamard, prime)
        expected = tuple(0 if i.bit_count() % 2 else
                         (2 * (1 - (-1) ** ((i & 3).bit_count()) * inverse)) % prime
                         for i in range(16))
        assert vector == normalize(expected, prime)
        assert parity(vector) == 0
        assert passes_four_port_identity(vector, (0, 1, 2, 3), 0, prime)


def check_field(prime):
    bases = projective_bases(prime)
    equal = tuple(int(index in (0, 7)) for index in range(8))
    clause = tuple(int(index != 0) for index in range(8))
    copy_allowed = shared_bases(equal, bases, prime)
    clause_dual = {inverse_transpose(b, prime) for b in shared_bases(clause, bases, prime)}
    assert len(bases) == prime * (prime ** 2 - 1) and not copy_allowed & clause_dual
    if prime == 2:
        assert not copy_allowed and not clause_dual

    def contract(index):
        left, right = index & 3, index >> 2
        return sum(equal[left * 2 + hidden] * clause[right * 2 + hidden]
                   for hidden in range(2)) % prime

    merged = tuple(contract(i) for i in range(16))
    assert merged == tuple(int((i & 1) == ((i >> 1) & 1) and (i & 13) != 0)
                           for i in range(16))
    # Right-leg basis sends (1,1) to (1,0) and (1,0) to (0,1).
    basis = (0, 1, 1, prime - 1)
    in_pair_axes = change_port(change_port(merged, 2, basis, prime), 3, basis, prime)
    pinned_zero_row = tuple(1 if i == 0 else (prime - 1 if i == 12 else 0)
                            for i in range(16))
    pinned_one_row = tuple(int(i == 3) for i in range(16))
    assert in_pair_axes == normalize(tuple((a + b) % prime
                                          for a, b in zip(pinned_zero_row, pinned_one_row)),
                                     prime)
    for component in (pinned_zero_row, pinned_one_row):
        assert parity(component) == 0
        assert all(passes_four_port_identity(component, order, 0, prime)
                   for order in permutations(range(4)))
    orbit = merged_orbit(merged, bases, prime)
    assert sum(orbit.values()) == len(bases) ** 4
    parity_count = 0
    for tensor, count in orbit.items():
        if prime == 2:
            assert complementary_sum(tensor) == 1
        p = parity(tensor)
        if p is not None:
            parity_count += count
            assert not any(passes_four_port_identity(tensor, order, p, prime)
                           for order in permutations(range(4)))
    assert parity_count > 0
    print(f"F_{prime} shared bases: {len(copy_allowed)} for COPY, {len(clause_dual)} "
          "dual-compatible with OR, intersection 0")
    print(f"Merged tensor: {sum(orbit.values())} projective basis tuples, "
          f"{len(orbit)} projective signatures, {parity_count} parity-compatible "
          "tuples, 0 meeting the four-port identity in any of 24 orders")


if __name__ == "__main__":
    for characteristic in (2, 3):
        check_field(characteristic)
    for characteristic in (3, 5, 7):
        check_degeneration(characteristic)
    print("Hadamard degeneration verified at all nonzero parameters in F_3, F_5 and F_7")
