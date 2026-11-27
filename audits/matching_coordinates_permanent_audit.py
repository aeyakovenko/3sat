"""Compare gadget perfect matchings with permutations and test quadratic inverses."""

from collections import Counter
from itertools import permutations
from math import prod
from random import Random


def matching_support(k, slack, rng):
    size = 2 * k * k + k + slack
    rows, columns = list(range(size)), list(range(size))
    rng.shuffle(rows)
    rng.shuffle(columns)
    edges = [[] for _ in rows]

    def arc(row, col, variable=0):
        edges[rows[row]].append((columns[col], variable))

    for i in range(k):
        for j in range(k):
            e = i * k + j
            middle = k + e
            private = k + k * k + e
            arc(i, private)
            arc(middle, private)
            arc(middle, middle, 1 << e)
            arc(private, middle)
            arc(private, j)
    for pad in range(2 * k * k + k, size):
        arc(pad, pad)

    result = Counter()

    def visit(left, free_cols, support):
        if not left:
            result[support] += 1
            return
        row = min(left, key=lambda r: sum(col in free_cols for col, _ in edges[r]))
        for col, variable in edges[row]:
            if col in free_cols:
                visit(left - {row}, free_cols - {col}, support | variable)

    visit(set(rows), set(columns), 0)
    expected = Counter(sum(1 << (i * k + j) for i, j in enumerate(pi))
                       for pi in permutations(range(k)))
    assert result == expected
    return sum(result.values())


def multiply(left, right, prime):
    size = len(left)
    return [sum(left[i] * right[j - i] for i in range(j + 1)) % prime
            for j in range(size)]


def inverse(a, x, k, prime):
    beta = (1 - a) % prime
    base = int(a == 0)
    derivative = (a + 2 * beta * base) % prime
    coeff = [base]
    for n in range(1, k + 1):
        cross = sum(coeff[i] * coeff[n - i] for i in range(1, n))
        coeff.append(((x if n == 1 else 0) - beta * cross)
                     * pow(derivative, -1, prime) % prime)
    square = multiply(coeff, coeff, prime)
    evaluated = [(a * u + beta * v) % prime for u, v in zip(coeff, square)]
    assert evaluated == [base, x] + [0] * (k - 1)
    return evaluated


def inverse_trials(rng):
    count = 0
    for prime in (3, 5, 7, 11):
        for k in range(1, 6):
            for a in range(prime):
                for x in range(prime):
                    inverse(a, x, k, prime)
                    count += 1
            values = [rng.randrange(prime) for _ in range(k * k)]
            entries = [inverse(rng.randrange(prime), x, k, prime) for x in values]
            recovered = direct = 0
            for pi in permutations(range(k)):
                series = [1] + [0] * k
                indices = [i * k + j for i, j in enumerate(pi)]
                for index in indices:
                    series = multiply(series, entries[index], prime)
                recovered += series[-1]
                direct += prod(values[index] for index in indices)
            assert (recovered - direct) % prime == 0
    return count


if __name__ == "__main__":
    rng = Random(837009)
    trials = terms = 0
    for k in range(1, 6):
        for slack in range(4):
            terms += matching_support(k, slack, rng)
            trials += 1
    print(f"{trials} labeled gadgets and {terms} perfect matchings")
    print(f"{inverse_trials(rng)} local inverses; 20 formal leading-coefficient checks")
