"""Exhaust low-degree perturbations of small shifted generalized inner products."""

from itertools import combinations


def monomial_columns(variables, degree):
    assignments = range(1 << variables)
    columns = []
    for size in range(degree + 1):
        for support in combinations(range(variables), size):
            selected = sum(1 << j for j in support)
            columns.append(sum(1 << x for x in assignments if x & selected == selected))
    return columns


def coordinates(order, rows, outputs):
    variables = (order + 1) * rows + outputs - 1
    result = [0] * outputs
    for x in range(1 << variables):
        for h in range(outputs):
            bit = 0
            for i in range(rows):
                positions = [a * rows + i for a in range(order)]
                positions.append(order * rows + i + h)
                bit ^= all((x >> p) & 1 for p in positions)
            result[h] |= bit << x
    return result


def audit(order, rows, outputs):
    variables = (order + 1) * rows + outputs - 1
    population = 1 << variables
    cols = monomial_columns(variables, order)
    bits = coordinates(order, rows, outputs)
    masks = [0]
    for column in bits:
        masks += [c ^ column for c in masks]
    maxima = [0] * len(masks)
    smallest_weight = population
    poly = 0
    for j in range(1 << len(cols)):
        if j:
            poly ^= cols[(j & -j).bit_length() - 1]
        if poly:
            smallest_weight = min(smallest_weight, poly.bit_count())
        for mask in range(1, len(masks)):
            correlation = abs(population - 2 * (masks[mask] ^ poly).bit_count())
            maxima[mask] = max(correlation, maxima[mask])
    assert smallest_weight == population >> order
    power = 1 << (order + 1)
    for peak in maxima[1:]:
        assert peak**power * (1 << order) ** rows <= population**power * ((1 << order) - 1) ** rows
    print(f"D={order}, rows={rows}, outputs={outputs}: {1 << len(cols)} phases,"
          f" mask maxima {maxima[1:]}/{population}, minimum weight {smallest_weight}")


if __name__ == "__main__":
    for case in ((1, 2, 2), (2, 1, 2), (3, 1, 1)):
        audit(*case)
