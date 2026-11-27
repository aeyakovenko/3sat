"""Check separate SAT witnesses for all field points on one fixed public RAM input."""

from collections import defaultdict
from itertools import product
from math import prod


def evaluation_row(coefficients, addresses, q):
    values = []
    for address in range(addresses):
        value = 0
        for coefficient in reversed(coefficients):
            value = (value * address + coefficient) % q
        values.append(value)
    return tuple(values)


def main():
    q, addresses, coefficients, prime = 7, 6, 4, 43
    rows = [evaluation_row(c, addresses, q) for c in product(range(q), repeat=coefficients)]
    assert len(set(rows)) == q**coefficients
    assert prime > q * addresses
    # e(address, value) = q * address + value is injective for read records.
    signatures = []
    alternates = []
    for challenge in range(prime):
        fibers = defaultdict(list)
        for idx, row in enumerate(rows):
            value = prod(challenge - q * address - v for address, v in enumerate(row)) % prime
            fibers[value].append(idx)
        digest = [None] * len(rows)
        alternative = [None] * len(rows)
        for value, indices in fibers.items():
            for i, idx in enumerate(indices):
                digest[idx] = value
                if len(indices) > 1:
                    alternative[idx] = indices[(i + 1) % len(indices)]
        signatures.append(digest)
        alternates.append(alternative)
    vulnerable = [idx for idx in range(len(rows)) if all(a[idx] is not None for a in alternates)]
    assert len(vulnerable) >= len(rows) - prime**2
    honest_index = vulnerable[0]
    honest = rows[honest_index]
    assert sum(x != y for x, y in zip(honest, honest)) == 0
    wrong_candidates = set()
    for challenge in range(prime):
        forged_index = alternates[challenge][honest_index]
        wrong_candidates.add(forged_index)
        assert sum(x != y for x, y in zip(honest, rows[forged_index])) >= addresses - coefficients + 1
        assert signatures[challenge][forged_index] == signatures[challenge][honest_index]
    # A single distinct row cannot work at every field point. Monic characteristic
    # polynomials have difference of degree at most addresses - 1.
    for idx in range(len(rows)):
        if idx != honest_index:
            assert sum(d[idx] == d[honest_index] for d in signatures) < addresses
    print(f"{len(vulnerable)}/{len(rows)} degree-bounded inputs fooled every separate challenge. "
          f"{len(wrong_candidates)} distinct false rows supplied {prime} fingerprints for one input; "
          f"all fixed false rows failed at least {prime-addresses+1} challenges.")


if __name__ == "__main__":
    main()
