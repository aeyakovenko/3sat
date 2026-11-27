"""Exercise the physical checksum CNFs, unique extensions, and binary scores."""
from itertools import product


def multiply(a, b):
    """GF(8) with modulus t^3+t+1."""
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a & 8:
            a ^= 0b1011
        b >>= 1
    return result


def indicator(index, point):
    value = 1
    for i, p in enumerate(point):
        value = multiply(value, p if index >> i & 1 else 1 ^ p)
    return value


def product_digit(a, b):
    return (a & b).bit_count() % 2


def and3(a, b, c):
    return [(-a, -b, c), (a, -c), (b, -c)]


def xor3(a, b, c):
    return [(a, b, -c), (a, -b, c), (-a, b, c), (-a, -b, -c)]


def build(coefficients, pin, first, second):
    # Values at 1 and 2 determine the whole base circuit, and its two gate outputs.
    clauses = [(1 if first else -1,), (2 if second else -2,)]
    clauses += xor3(1, 2, 3) + and3(1, 3, 4)
    running = 5
    clauses.append((-running,))
    for v, coefficient in enumerate(coefficients, 1):
        selector, masked, after = running + 1, running + 2, running + 3
        clauses.append((selector if coefficient else -selector,))
        clauses += and3(selector, v, masked) + xor3(running, masked, after)
        running = after
    clauses.append((running if pin else -running,))
    return running, clauses


def exact_three(n, clauses):
    pad = tuple(range(n + 1, n + 4))
    banned = [tuple(-p if (a >> i) & 1 else p for i, p in enumerate(pad))
              for a in range(1, 8)]
    for clause in clauses:
        banned.append(tuple(clause) + pad[:3 - len(clause)])
    assert all(len(set(map(abs, c))) == len(c) == 3 for c in banned)
    return n + 3, banned


def count_models(n, clauses):
    """DPLL counts every fully specified assignment, including any unused bits."""
    def visit(assign):
        while True:
            forced = {}
            for clause in clauses:
                if any(assign.get(abs(lit)) == (lit > 0) for lit in clause):
                    continue
                free = [lit for lit in clause if abs(lit) not in assign]
                if not free:
                    return 0
                if len(free) == 1:
                    lit = free[0]
                    val = lit > 0
                    if forced.get(abs(lit), val) != val:
                        return 0
                    forced[abs(lit)] = val
            if not forced:
                break
            assign.update(forced)
        if len(assign) == n:
            return 1
        key = next(i for i in range(n, 0, -1) if i not in assign)
        return sum(visit(assign | {key: b}) for b in (False, True))
    return visit({})


def check_printed_formulas():
    seen = {}
    shape = {}
    count = 0
    for first, second in product(range(2), repeat=2):
        table = (first, second, first ^ second, first & (first ^ second))
        yes = 0
        for p, q, lam in product(range(8), repeat=3):
            weights = [indicator(i, (p, q)) for i in range(4)]
            symbol = 0
            for value, multiplier in zip(table, weights):
                if value:
                    symbol ^= multiplier
            coefficients = tuple(product_digit(lam, w) for w in weights)
            for pin in range(2):
                key = coefficients, pin, first, second
                expected = int(product_digit(lam, symbol) == pin)
                n, clauses = build(coefficients, pin, first, second)
                if key not in seen:
                    seen[key] = (count_models(n, clauses), count_models(*exact_three(n, clauses)))
                assert seen[key] == (expected, expected)
                arities = tuple(len(c) for c in clauses)
                assert shape.setdefault("arities", arities) == arities
                yes += expected
                count += 1
        assert yes == 8 ** 3
    return count, len(seen)


def scores_and_curves():
    for rule in range(1 << 8):
        scores = []
        for symbol in range(8):
            agreement = sum((rule >> lam & 1) == product_digit(lam, symbol)
                            for lam in range(8))
            scores.append(2 * agreement - 8)
        assert sum(x * x for x in scores) == 64
    pairs = 0
    for t, u in product(range(1, 8), repeat=2):
        if t == u:
            continue
        points = {(multiply(a, t) ^ multiply(b, multiply(t, t)),
                   multiply(a, u) ^ multiply(b, multiply(u, u)))
                  for a, b in product(range(8), repeat=2)}
        assert len(points) == 64
        pairs += 1
    return pairs


if __name__ == "__main__":
    draws, physical_counts = check_printed_formulas()
    print(f"{draws:,} binary checksum draws, {physical_counts} pairs of explicit CNF model counts")
    print(f"256 Walsh score arrays and {scores_and_curves()} quadratic-curve marginals checked")
