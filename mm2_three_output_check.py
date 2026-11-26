"""Verify six ANDs for every rank-three projection of binary 2-by-2 MM.

With --all, test all homogeneous first-factor normals for both inequivalent
projections. By default, compute and test one representative per stabilizer
orbit. Both modes test all surviving first gates on the full truth table.
"""

import argparse
from itertools import combinations

from mm2_and_exhaustion import independent, one_extra
from mm2_six_gate_restrictions import coordinate_changes, parity, pullback, target


def linear_image(x, columns):
    value = 0
    for j, column in enumerate(columns):
        if (x >> j) & 1:
            value ^= column
    return value


def coordinates(kernel):
    """Three independent output functionals vanishing on the kernel."""
    basis = independent([u for u in range(1, 16) if not parity(u, kernel)])
    assert len(basis) == 3
    return basis


def strassen_six(x, kernel):
    """Omit the product with output mask 8 or 9, then take quotient outputs."""
    a, b, c, d, e, f, g, h = [(x >> j) & 1 for j in range(8)]
    terms = [
        (9, a ^ d, e ^ h), (12, c ^ d, e), (10, a, f ^ h),
        (5, d, g ^ e), (3, a ^ b, h), (8, c ^ a, e ^ f), (1, b ^ d, g ^ h),
    ]
    remaining = [(v, left, right) for v, left, right in terms if v != kernel]
    assert len(remaining) == 6
    value = 0
    for output_mask, left, right in remaining:
        if left & right:
            value ^= output_mask
    return value


def table(values):
    return sum(value << index for index, value in enumerate(values))


def four_ands_on(kernel, points, free_dimension, first_gate=None):
    """Decide four further ANDs, optionally providing one product for free."""
    inputs = independent([table((x >> j) & 1 for x in points) for j in range(8)])
    if first_gate is not None:
        a, b = first_gate
        inputs.append(table(parity(a, x) & parity(b, x) for x in points))
    assert points[0] == 0 and len(inputs) == len(independent(inputs)) == free_dimension
    outputs = [table(parity(mask, target(x)) for x in points) for mask in coordinates(kernel)]
    assert len(independent(inputs + outputs)) - len(inputs) == 3
    feasible, _, _ = one_extra(inputs, outputs, (1 << len(points)) - 1)
    return feasible


def on_hyperplane(kernel, normal):
    points = [x for x in range(256) if not parity(x, normal)]
    assert len(points) == 128
    return four_ands_on(kernel, points, 7)


def check(kernel, changes, all_normals):
    for x in range(256):
        assert strassen_six(x, kernel) ^ target(x) in (0, kernel)
    stabilizer = [inputs for inputs, inverse_output in changes
                  if linear_image(kernel, inverse_output) == kernel]
    pending = set(range(1, 256))
    viable = set()
    representatives = 0
    while pending:
        normal = min(pending)
        orbit = {pullback(normal, inputs) for inputs in stabilizer}
        assert normal in orbit and orbit <= pending
        pending -= orbit
        representatives += 1
        feasible = on_hyperplane(kernel, normal)
        if all_normals:
            for other in sorted(orbit - {normal}):
                assert on_hyperplane(kernel, other) == feasible
        if feasible:
            viable.update(orbit)

    # Pick the two smallest vectors in each unordered two-dimensional plane.
    planes = [(a, b, a ^ b) for a, b in combinations(sorted(viable), 2)
              if b < (a ^ b) and (a ^ b) in viable]
    for a, b, _ in planes:
        assert not four_ands_on(kernel, range(256), 9, first_gate=(a, b))
        three_quarters = [x for x in range(256) if not (parity(a, x) and parity(b, x))]
        assert len(three_quarters) == 192
        assert not four_ands_on(kernel, three_quarters, 8)
    expected = {8: [(1, 2, 3), (16, 64, 80)], 9: []}
    assert planes == expected[kernel]
    assert viable == ({1, 2, 3, 16, 64, 80} if kernel == 8 else set())
    print(f'Kernel {kernel}: {representatives} input-normal orbits; '
          f'four-AND slices {sorted(viable)}; rejected first-gate planes {planes}.', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--all', action='store_true', help='check all 510 projection/slice pairs directly')
    args = parser.parse_args()
    changes = list(coordinate_changes())
    orbits = [{linear_image(kernel, inverse_output) for _, inverse_output in changes}
              for kernel in (8, 9)]
    assert sorted(map(len, orbits)) == [6, 9] and not orbits[0].intersection(orbits[1])
    assert orbits[0] | orbits[1] == set(range(1, 16))
    for kernel in (8, 9):
        check(kernel, changes, args.all)
    print('All 15 three-output quotients have exact AND complexity six.')
    print('Four ANDs excluded on the three-quarter domain for both surviving planes.')


if __name__ == '__main__':
    main()
