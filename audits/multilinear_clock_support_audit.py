"""Check multilinear support with dense wrapper and independent raw slices."""
from itertools import product
from math import prod


def probe_support_tables():
    cases = 0
    for prime in (3, 5):
        for arity in range(1, 6):
            cube = tuple(product((0, 1), repeat=arity))
            # Two positive dense-tag tables plus a fixed independent slice.
            base = {u: int(u[0] == 0 and sum(u) % 2 == 0) for u in cube}
            dense = {u for u in cube if u[0] and 2 * sum(u) > arity}
            for point in product(range(prime), repeat=arity):
                if 2 * sum(x != 0 for x in point) > arity:
                    continue
                weights = {u: prod(x if bit else 1 - x for bit, x in zip(u, point)) % prime
                           for u in cube}
                assert all(weights[u] == 0 for u in dense)
                baseline = sum(weights[u] * base[u] for u in cube) % prime
                enriched = sum(weights[u] * (base[u] or u in dense) for u in cube) % prime
                assert baseline == enriched
                cases += 1
    return cases


if __name__ == "__main__":
    print(f"{probe_support_tables()} sparse extension queries preserved across dense-slice changes")
