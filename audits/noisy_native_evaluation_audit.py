"""Exact noisy-circuit probabilities and cluster truncation on small reconvergent DAGs."""
from fractions import Fraction
from itertools import product
from random import Random

from gate_fault_spectrum_audit import gate_value, run


def near_gates(gates, depth):
    retained = set()
    frontier = {len(gates) - 1}
    for _ in range(depth):
        retained.update(frontier)
        frontier = {p for i in frontier for p in gates[i][:2] if p is not None} - retained
    return retained


def noisy_probability(gates, rho, retained):
    ids = sorted(retained)
    a = (1 - rho) / 2
    probability = 0
    for bits in range(1 << len(ids)):
        value = 0
        for k, i in enumerate(ids):
            value |= (gate_value(gates[i], value) ^ ((bits >> k) & 1)) << i
        if value >> (len(gates)-1):
            flips = bits.bit_count()
            probability += a ** flips * (1-a) ** (len(ids)-flips)
    return probability


def check_cuts(gates):
    total = 0
    for rho in (Fraction(1, 2), Fraction(2, 3), Fraction(7, 10)):
        actual = noisy_probability(gates, rho, set(range(len(gates))))
        survival = Fraction(1)
        for d in range(1, 5):
            survival = rho * rho * survival * (2 - survival)
            clipped = noisy_probability(gates, rho, near_gates(gates, d))
            # 1.387 is an upper rational approximation of 2 ln(2).
            assert (clipped - actual) ** 2 <= Fraction(1387, 1000) * survival
            assert survival <= Fraction(2, d+2)
            total += 1
    return total


def check_lazy(gates):
    n = len(gates)
    capped = [0] * (n + 1)
    size_counts = [0] * (n + 1)
    for modes in product(range(4), repeat=n):
        visited = {}

        def discover(node):
            if node not in visited:
                if modes[node] < 2:
                    y = sum(discover(i) << i for i in set(gates[node][:2]) if i is not None)
                    visited[node] = gate_value(gates[node], y)
                else:
                    visited[node] = modes[node] & 1
            return visited[node]
        result = discover(n - 1)
        size_counts[len(visited)] += 1
        for limit in range(len(visited), n+1):
            capped[limit] += result
    assert Fraction(capped[n], 4 ** n) == noisy_probability(gates, Fraction(1, 2), set(range(n)))
    assert sum(capped[i] - capped[i-1] for i in range(1, n + 1)) == capped[n]
    assert sum(size_counts) == 4 ** n
    return 4 ** n


if __name__ == "__main__":
    rng = Random(1459)
    cut_checks = lazy_checks = 0
    for n in range(2, 8):
        for _ in range(7):
            gates = [(None, None, rng.randrange(2))]
            gates.extend((rng.randrange(i), rng.randrange(i), rng.randrange(16)) for i in range(1, n))
            cut_checks += check_cuts(gates)
            if n <= 5:
                lazy_checks += check_lazy(gates)
    print(f"{cut_checks} truncated cone bounds; {lazy_checks:,} lazy noisy runs")
