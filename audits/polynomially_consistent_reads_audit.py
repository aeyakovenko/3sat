"""Check optimality from the full finite constraint matrix and test forged CPU reads."""

from itertools import product
from math import prod


def dimension(rows, columns, q):
    pivots = {}
    for original in rows:
        row = [x % q for x in original]
        for j, value in enumerate(row):
            if not value:
                continue
            if j not in pivots:
                inv = pow(value, -1, q)
                pivots[j] = [(inv * x) % q for x in row]
                break
            previous = pivots[j]
            for k in range(j, columns):
                row[k] = (row[k] - value * previous[k]) % q
    return columns - len(pivots)


def full_constraint_rows(T, d, r, q):
    powers = {
        a: [sum(pow(j, k, q) * pow(a, j, q) for j in range(T)) % q for k in range(r + 1)]
        for a in range(q)
    }
    for points in product(range(q), repeat=d):
        factors = [
            prod(points[i] for i in range(d) if mask & (1 << i)) % q
            for mask in range(1 << d)
        ]
        for a in set(points):
            yield [u * v for u in factors for v in powers[a]]


def audit_forgery(T, d, q):
    def guard(j):
        return prod((j + h) * (j - T + h) for h in range(1, d + 1)) % q

    least_errors = T
    for points in product(range(q), repeat=d):
        values = [guard(j) for j in range(-d, T)]
        for a in points:
            values = [(left - a * right) % q for left, right in zip(values, values[1:])]
        assert len(values) == T
        errors = sum(bool(v) for v in values)
        assert errors >= T - 2 * d
        assert 2 * errors >= T
        assert all(sum(v * pow(a, j, q) for j, v in enumerate(values)) % q == 0 for a in points)
        least_errors = min(least_errors, errors)
    return least_errors


def main():
    for T, d, q in ((6, 1, 11), (9, 2, 13)):
        result = []
        for r in range(T - d):
            cols = (r + 1) * 2**d
            nullity = dimension(full_constraint_rows(T, d, r, q), cols, q)
            assert nullity == max(0, r - 2 * d + 1)
            result.append(nullity)
        print(f"T={T}, d={d}, q={q}, kernel dimensions {result}")

    for T, d, q in ((6, 1, 11), (9, 2, 13), (13, 3, 17)):
        least = audit_forgery(T, d, q)
        print(f"{q**d} challenge tuples, at least {least} forged nonzero reads among {T}")


if __name__ == "__main__":
    main()
