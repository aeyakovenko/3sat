"""Finite checks for the permutation-family clauses and semantic cut shortcuts."""

from itertools import combinations, permutations, product
from math import ceil, factorial, log2


def clauses(left, right):
    m = len(left)
    result = []

    def unit_or_short(*literals):
        result.append(literals + (literals[-1],) * (3 - len(literals)))

    bits = []
    for i in range(m):
        z = 1 + i
        wl = 1 + m + left[i]
        wr = 1 + m + right[i]
        bit = 1 + 2 * m + i
        unit_or_short(-z, wl)
        unit_or_short(z, -wl)
        for z_value, w_value, claimed in product((0, 1), repeat=3):
            if claimed != z_value ^ w_value:
                unit_or_short(-z if z_value else z, -wr if w_value else wr,
                              -bit if claimed else bit)
        bits.append(bit)
    acc = bits[0]
    for j, bit in enumerate(bits[1:]):
        out = 3 * m + j + 1
        unit_or_short(-acc, out)
        unit_or_short(-bit, out)
        unit_or_short(acc, bit, -out)
        acc = out
    unit_or_short(acc)
    return result


def brute_sat(cnf):
    width = max(abs(x) for clause in cnf for x in clause)
    for mask in range(1 << width):
        if all(any(bool(mask & (1 << (abs(lit) - 1))) == (lit > 0)
                   for lit in clause) for clause in cnf):
            return True
    return False


def longest_monotone(values, group):
    for length in range(len(group), 0, -1):
        for indices in combinations(group, length):
            ordered = [values[i] for i in indices]
            if ordered == sorted(ordered):
                return indices, True
            if ordered == sorted(ordered, reverse=True):
                return indices, False
    raise ValueError("the group is empty")


def cut_terms(pi, d):
    m = len(pi)
    side = m // d
    width = side * side
    hidden = []
    weights = [0] * m
    for start in range(0, m, width):
        group = list(range(start, min(m, start + width)))
        indices, increasing = longest_monotone(pi, group)
        hidden.extend(indices[:d - len(hidden)])
        for i in group:
            weights[i] = i + 1 if increasing else m - i
    assert len(hidden) == d
    # Off-domain labels are deliberately arbitrary, including valid group values.
    labels = [v % ceil(m / width) for v in range(m)]
    for i in hidden:
        labels[pi[i]] = i // width
    return hidden, weights, labels, width


def scores(seq, weights, labels, width):
    return (sum(labels[value] == i // width for i, value in enumerate(seq)),
            sum(w * v for w, v in zip(weights, seq)))


def binary_remainder(value, divisor):
    while value and value.bit_length() >= divisor.bit_length():
        value ^= divisor << (value.bit_length() - divisor.bit_length())
    return value


def irreducible(poly):
    degree = poly.bit_length() - 1
    return all(binary_remainder(poly, divisor) for k in range(1, degree // 2 + 1)
               for divisor in range(1 << k, 2 << k))


def extend_labels(keys, labels, size, degree):
    for poly in range(1 << degree, 2 << degree):
        if not irreducible(poly):
            continue
        pivots = {}
        for key, label in zip(keys, labels):
            vector = binary_remainder(1 << key, poly)
            while vector:
                lead = vector.bit_length() - 1
                if lead not in pivots:
                    pivots[lead] = vector, label
                    break
                old_vector, old_label = pivots[lead]
                vector ^= old_vector
                label ^= old_label
            if not vector:
                break
        if len(pivots) == len(keys):
            break
    else:
        raise ValueError("no independent residues")

    initials = []
    for bit in range(degree):
        vector = 1 << bit
        label = 0
        while vector:
            lead = vector.bit_length() - 1
            old_vector, old_label = pivots.get(lead, (1 << lead, 0))
            vector ^= old_vector
            label ^= old_label
        initials.append(label)
    seq = list(initials)
    for v in range(size - degree):
        new = 0
        for j in range(degree):
            if poly >> j & 1:
                new ^= seq[v + j]
        seq.append(new)
    assert [seq[key] for key in keys] == list(labels)


def main():
    cnfs = 0
    for m in (1, 2, 3):
        perms = list(permutations(range(m)))
        for left, right in product(perms, repeat=2):
            assert brute_sat(clauses(left, right)) == (left != right)
            cnfs += 1

    hybrids = single_score_collisions = 0
    for pi in permutations(range(6)):
        for d in range(1, len(pi) + 1):
            hidden, weights, labels, width = cut_terms(pi, d)
            target = scores(pi, weights, labels, width)
            for moved in permutations(pi[i] for i in hidden):
                sigma = list(pi)
                for i, value in zip(hidden, moved):
                    sigma[i] = value
                score = scores(sigma, weights, labels, width)
                assert (score == target) == (tuple(sigma) == pi)
                if score[1] == target[1] and score[0] != target[0]:
                    single_score_collisions += 1
                hybrids += 1
    assert single_score_collisions
    trials = 0
    for keys in combinations(range(7), 3):
        for labels in product(range(3), repeat=3):
            extend_labels(keys, labels, 7, 5)
            trials += 1
    for keys in combinations((1, 3, 8, 12, 17, 22, 28, 30), 4):
        degree = len(keys) + ceil(log2(4 * 31)) + 2
        extend_labels(keys, (0, 1, 2, 3), 31, degree)
        trials += 1
    bits = (factorial(256) - 1).bit_length()
    print(f"{cnfs} full CNFs and {hybrids} permitted hybrids passed. "
          f"Removing the group-count test gives {single_score_collisions} false equalities. "
          f"{trials} binary recurrence label extensions passed. "
          f"256 prescribed omissions require {bits} bits at fixed length.")


if __name__ == "__main__":
    main()
