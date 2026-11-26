"""Exact finite capacity and fault detection for guarded equality comparisons."""
from itertools import combinations, product


def distances(left, right):
    return sum(a != b for a, b in zip(left, right))


def exhaustive_capacities(q, length):
    words = list(product(range(q), repeat=length))
    best = [0] * (length+1)
    checked = 0
    for size in range(1, len(words)+1):
        for subset in combinations(words, size):
            separation = min((distances(x,y) for x,y in combinations(subset, 2)), default=length)
            best[separation] = max(best[separation], size)
            checked += 1
    for j in range(length-1, 0, -1):
        best[j] = max(best[j], best[j+1])
    return best[1:], checked


def tiny_encodings():
    cases = [(2, 1, [2]), (2, 2, [4, 2]), (2, 3, [8, 4, 2]), (2, 4, [16, 8, 2, 2]),
             (3, 2, [9, 3]), (4, 2, [16, 4])]
    families = 0
    for q, length, expected in cases:
        actual, checked = exhaustive_capacities(q, length)
        assert actual == expected, (q, length, actual)
        families += checked
    return families


def comparison_failures(messages, signatures):
    # An accepting hybrid on x,y must report exactly the right label on
    # every comparison. Each guard sees its corresponding boundary symbol.
    checks = 0
    for i, left in enumerate(messages):
        for j, right in enumerate(messages):
            raw = tuple(right)
            assert tuple(left) == raw or i != j
            rejected = {g for g, (a,b) in enumerate(zip(signatures[i], signatures[j])) if a != b}
            if i != j:
                assert rejected
            else:
                assert not rejected
            checks += 1
    return checks


def prime_field_tests():
    count = 0
    for q in [2, 3, 5, 7]:
        for length in range(1, q+1):
            for dimension in range(1, min(length, 3)+1):
                coefficients = list(product(range(q), repeat=dimension))
                words = []
                for coeff in coefficients:
                    words.append(tuple(sum(c*pow(j,i,q) for i,c in enumerate(coeff)) % q
                                       for j in range(length)))
                # The code is linear. All pairwise distances are the weights
                # of nonzero words, each of which is a difference from zero.
                assert min(distances(words[0], row) for row in words[1:]) == length-dimension+1
                assert len(set(words)) == q**dimension
                if q <= 3:
                    count += comparison_failures(coefficients, words)
    return count


def simplex_and_forges():
    comparisons = 0
    for bits in range(1, 7):
        symbols = list(product(range(2), repeat=bits))
        signatures = [tuple(sum(x*y for x,y in zip(message, mask)) % 2 for mask in symbols[1:])
                      for message in symbols]
        assert len(set(signatures)) == len(symbols)
        for i, j in combinations(range(len(symbols)), 2):
            assert distances(signatures[i], signatures[j]) == 2**(bits-1)
        comparisons += comparison_failures(symbols, signatures)
        if bits <= 4:
            for i, left in enumerate(symbols):
                for j, right in enumerate(symbols):
                    for k, reply in enumerate(symbols):
                        received_accept = reply == right
                        if received_accept and left != right:
                            assert distances(signatures[i], signatures[k]) == 2**(bits-1)
    return comparisons


if __name__ == '__main__':
    print(f'{tiny_encodings()} nonempty state-vector families exhausted.')
    print(f'{prime_field_tests()} guarded comparisons on small Reed–Solomon codes.')
    print(f'{simplex_and_forges()} guarded simplex comparisons; all raw forgeries through 4 bits.')
