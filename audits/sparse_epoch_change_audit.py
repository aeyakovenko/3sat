"""Newton expansion on actual sparse rows, including suffix overwrite behavior."""
from fractions import Fraction
from itertools import combinations, product
from math import comb
from sparse_reply_cut_audit import make_filter


def subsets(elements, max_size):
    for i in range(min(len(elements), max_size)+1):
        yield from map(frozenset, combinations(elements, i))


def newton(values):
    result = []
    while values:
        result.append(values[0])
        values = [b-a for a, b in zip(values, values[1:])]
    return result


def check_expansion():
    cells = range(7)
    cases = 0
    for w in (0, 2, 4):
        values = [make_filter(w, 0, 2)(i) for i in range(w+1)]
        for grid in (values, [Fraction((-1)**i, i+1) for i in range(w+1)]):
            coeff = newton(grid)
            assert all(abs(c) <= 2**i for i, c in enumerate(coeff))
            for old in subsets(cells, w):
                row_terms = list(subsets(old, w))
                for tested in subsets(cells, len(cells)):
                    n = len(old & tested)
                    assert sum(c for i, c in enumerate(coeff) for _ in range(comb(n, i))) == grid[n]
                    assert sum(coeff[len(t)] for t in row_terms if t <= tested) == grid[n]
                    cases += 1
    return cases


def suffix(memory, x, y):
    # Abort label for a pin read is tracked independently of the returned sign.
    written = set()
    incoming = set()
    queried_pin = False
    state = list(memory)
    val = y
    for step in range(11):
        a = (val + step*step + y) % len(state)
        if (val+step) % 5 == 0:
            written.add(a)
            state[a] = val % 3
        elif (val+step) % 7 == 0:
            queried_pin = True
            val += x
        else:
            if a not in written:
                incoming.add(a)
            val = (val+state[a])*3 % 19
    return (-1 if val % 2 else 1), queried_pin, incoming


def check_retrieval():
    cases = 0
    for start in product(range(2), repeat=4):
        for end in product(range(3), repeat=4):
            changed = {i for i, (a, b) in enumerate(zip(start, end)) if a != b}
            for y in range(5):
                base_sign, base_pin, base_reads = suffix(start, 0, y)
                for x in range(2):
                    sign, pin, reads = suffix(end, x, y)
                    actual = 0 if pin or reads & changed else sign
                    formula = 0 if base_pin or base_reads & changed else base_sign
                    assert actual == formula
                    cases += 1
    return cases


if __name__ == "__main__":
    print(f"{check_expansion()} sparse intersection expansions and {check_retrieval()} adaptive suffix cases passed")
