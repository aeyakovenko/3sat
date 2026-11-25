"""Exhaust the directions of affine flats on the 2-by-2 binary matrix-product graph."""

from collections import Counter
from itertools import combinations, product


def apply(matrix, vector, d):
    image = 0
    mask = (1 << d) - 1
    for col in range(d):
        if (vector >> col) & 1:
            image ^= (matrix >> (d * col)) & mask
    return image


def matrix_product(a, b, d):
    return sum(apply(a, apply(b, 1 << i, d), d) << (d * i) for i in range(d))


def vector_span(rows):
    result = [0]
    for row in rows:
        result += [value ^ row for value in result]
    return frozenset(result)


def spaces(width, compatible):
    """Visit compatible spaces exactly once, by their unique reduced echelon basis."""
    for rank in range(width + 1):
        for pivots in combinations(range(width), rank):
            rows = []
            for pivot in pivots:
                free = [1 << bit for bit in range(pivot + 1, width) if bit not in pivots]
                rows.append([value | (1 << pivot) for value in vector_span(free)])

            def extend(basis):
                if len(basis) == rank:
                    yield tuple(basis)
                    return
                for row in rows[len(basis)]:
                    if all(compatible(row, other) for other in basis):
                        yield from extend([*basis, row])

            yield from extend([])


def audit_effective_dimensions(flat, a_part, b_part, d):
    inputs = range(1 << d)
    a_space = {a_part[pair] for pair in flat}
    kernel = {v for v in inputs if all(apply(a, v, d) == 0 for a in a_space)}
    coset_id = [min(k ^ v for k in kernel) for v in inputs]
    column_spaces = [{coset_id[apply(b_part[pair], v, d)] for pair in flat} for v in inputs]
    lifted_support = set(kernel)
    for representatives in column_spaces:
        for v in representatives:
            lifted_support |= {u ^ v for u in lifted_support}
    h_maps = {tuple(coset_id[apply(b_part[pair], 1 << i, d)] for i in range(d))
              for pair in flat}
    restricted_maps = {tuple(apply(a, v, d) for v in sorted(lifted_support)) for a in a_space}
    dim = lambda size: size.bit_length() - 1
    m = d - dim(len(kernel))
    u = d * m - dim(len(a_space))
    s = dim(len(lifted_support)) - dim(len(kernel))
    t = max(dim(len(image)) for image in column_spaces)
    h = dim(len(h_maps))
    assert len(h_maps) == len(restricted_maps)
    assert (d - 1)*t <= u and d*s - u <= h <= t*(s - t + 1)


def enumerate_flats(d):
    words = 1 << (d * d)
    product_table = [[matrix_product(a, b, d) for b in range(words)] for a in range(words)]
    vectors = range(words**2)
    a_part = [pair % words for pair in vectors]
    b_part = [pair // words for pair in vectors]
    product_at = [product_table[a][b] for a, b in zip(a_part, b_part)]

    def polar_zero(pair, other):
        return (product_table[a_part[pair]][b_part[other]]
                == product_table[a_part[other]][b_part[pair]])

    subspaces = [vector_span(basis) for basis in spaces(d, lambda u, v: True)]
    split_charts = {}
    for kernel in subspaces:
        split_charts[kernel] = frozenset(pair for pair in vectors
            if all(apply(a_part[pair], k, d) == 0 for k in kernel)
            and all(apply(b_part[pair], 1 << i, d) in kernel for i in range(d)))

    boundary_dim = d*d - d + 1
    nonsplit_boundary = set()
    counts = Counter()
    for basis in spaces(2*d*d, polar_zero):
        rank = len(basis)
        # Membership in a split chart need only be tested on the basis.
        containers = sum(all(row in chart for row in basis) for chart in split_charts.values())
        assert rank <= d*d
        if rank >= boundary_dim:
            assert containers <= 1
        if rank > boundary_dim:
            assert containers == 1
        if containers == 0 and rank == boundary_dim:
            nonsplit_boundary.add(vector_span(basis))
        counts[rank, containers == 0] += 1
        # Polar vanishing gives a genuine *linear* graph direction over F2.
        flat = vector_span(basis)
        audit_effective_dimensions(flat, a_part, b_part, d)
        for row in basis:
            assert all(product_at[row ^ other] == product_at[row] ^ product_at[other]
                       for other in flat)

    constructed = set()
    for kernel in subspaces:
        for z in range(1, 1 << d):
            # Unique representative for a nonzero line in the binary quotient.
            if z != min(z ^ k for k in kernel):
                continue
            for y, ell in product(range(1, 1 << d), repeat=2):
                flat = set()
                for pair in vectors:
                    a, b = a_part[pair], b_part[pair]
                    if any(apply(a, k, d) for k in kernel):
                        continue
                    az = apply(a, z, d)
                    if az not in (0, y):
                        continue
                    expected = z if az == y else 0
                    if all((apply(b, 1 << i, d) ^ (expected if (ell >> i) & 1 else 0)) in kernel
                           for i in range(d)):
                        flat.add(pair)
                direction = frozenset(flat)
                assert len(direction) == 1 << boundary_dim and direction not in constructed
                constructed.add(direction)
    assert constructed == nonsplit_boundary
    return counts


def audit_shifted_pins(d):
    width = d*d
    words = 1 << width
    cyclic = sum((1 << ((i + 1) % d)) << (d*i) for i in range(d))
    left_shift = [matrix_product(cyclic, a, d) for a in range(words)]
    right_shift = [matrix_product(b, cyclic, d) for b in range(words)]
    output = [[matrix_product(a, b, d) ^ left_shift[a] ^ right_shift[b]
               for b in range(words)] for a in range(words)]
    for a, b in product(range(words), repeat=2):
        for bit in range(width):
            assert output[a ^ (1 << bit)][b] != output[a][b]
            assert output[a][b ^ (1 << bit)] != output[a][b]


if __name__ == '__main__':
    counts = enumerate_flats(2)
    for dim in range(5):
        print(f'dim={dim} split={counts[dim, False]} nonsplit={counts[dim, True]}')
    audit_shifted_pins(2)
    print('All 2x2 binary product flats checked; all shifted pin sensitivities checked.')
