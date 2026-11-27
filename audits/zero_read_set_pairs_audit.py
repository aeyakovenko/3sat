"""Exact small tests for sparse marked words at a cut in equality-SAT."""
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb


def subset_table(alphabet, marks):
    slots = marks
    while comb(slots, marks) < alphabet:
        slots += 1
    return slots, list(combinations(range(slots), marks))[:alphabet]


def encode_groups(raw, alphabet, group, table):
    codes = []
    for start in range(0, len(raw) - group + 1, group):
        rank = 0
        for digit in raw[start:start + group]:
            rank = alphabet * rank + digit
        codes.append(frozenset(table[rank]))
    return codes


def slice_audit(alphabet, rows, group, marks):
    slots, table = subset_table(alphabet**group, marks)
    universe = set(range(slots))
    vectors = tuple(product(range(alphabet), repeat=rows))
    encoded = {v: encode_groups(v, alphabet, group, table) for v in vectors}
    tested = 0
    for left, right in product(vectors, repeat=2):
        support = {(i, v) for i, code in enumerate(encoded[left]) for v in code}
        tests = [(i, v) for i, code in enumerate(encoded[right]) for v in sorted(universe - code)]
        zero_count = sum(key not in support for key in tests)
        cutoff = rows // group * group
        assert (zero_count == len(tests) and left[cutoff:] == right[cutoff:]) == (left == right)
        # The SAT predicate on the same layout: can Boolean labels separate two named values?
        sat = any(any(labels[a] != labels[b] for a, b in zip(left, right))
                  for labels in product(range(2), repeat=alphabet))
        assert sat == (left != right)
        positives = {(i, a) for i, a in enumerate(left)}
        assert all((i, b) in positives for i, b in enumerate(right)) == (not sat)
        assert len(support) == (rows//group)*marks
        if left == right:
            assert zero_count == (rows//group)*(slots-marks)
        tested += 1
    return tested


def ordered_pairs(universe_size, marks):
    universe = set(range(universe_size))
    families = [(set(a), universe-set(a)) for a in combinations(universe, marks)]
    probability = sum((Fraction(1, comb(len(a)+len(b), len(a))) for a,b in families), Fraction())
    assert probability == 1
    separated = 0
    for order in permutations(universe):
        rank = {a: i for i, a in enumerate(order)}
        passing = [a for a,b in families if max((rank[x] for x in a), default=-1)
                   < min((rank[x] for x in b), default=universe_size)]
        assert len(passing) == 1
        separated += 1
    return separated


def four_entry_tradeoff(m):
    # One positive probe for the first two digits. Three negative banks
    # represent the remaining m² possibilities in a smaller radix.
    base = 1
    while base**3 < m*m:
        base += 1
    def split(raw):
        value = m*raw[2] + raw[3]
        digits = []
        for _ in range(3):
            value, digit = divmod(value, base)
            digits.append(digit)
        return (m*raw[0]+raw[1], digits)
    count = 0
    all_groups = list(product(range(m), repeat=4))
    for x,y in product(all_groups, repeat=2):
        px,dx = split(x)
        py,dy = split(y)
        stores = {('p',px)} | {(j,d) for j,d in enumerate(dx)}
        probes = [(j,b) for j,d in enumerate(dy) for b in range(base) if b != d]
        assert len(stores) == 4 and len(probes) == 3*(base-1)
        assert ((('p',py) in stores) and all(q not in stores for q in probes)) == (x == y)
        count += 1
    return count


def balanced_code_audit():
    total = 0
    for bits in range(1, 13):
        length = 2
        while comb(length, length//2) < 2**bits:
            length += 2
        seen = set()
        for number in range(2**bits):
            rank = number
            count = comb(length, length//2)
            remaining = length//2
            marks = []
            for step in range(length):
                slots = length - step
                without = count * (slots - remaining) // slots
                if rank < without:
                    count = without
                else:
                    marks.append(step)
                    rank -= without
                    count -= without
                    remaining -= 1
            assert rank == 0 and remaining == 0 and count == 1
            assert len(marks) == length//2 and tuple(marks) not in seen
            seen.add(tuple(marks))
            total += 1
    return total


if __name__ == '__main__':
    comparisons = sum(slice_audit(*params) for params in
                      [(2,4,1,1), (2,4,2,1), (2,4,2,2), (3,3,1,2), (3,3,2,1)])
    orders = sum(ordered_pairs(n, k) for n in range(1,8) for k in range(n+1))
    print(f'{comparisons} pairs of SAT blocks, with exact sparse-mark and zero-probe counts.')
    print(f'{four_entry_tradeoff(3)} mixed-positive four-entry comparisons.')
    print(f'{orders} total orders with exactly one separated pair in the extremal families.')
    print(f"{balanced_code_audit()} balanced block encodings with streaming binomial updates.")
