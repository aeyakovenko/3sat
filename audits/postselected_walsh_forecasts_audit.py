"""Finite tests for fractional Walsh rounding and projected conditioned counts."""

from fractions import Fraction
from itertools import product
from random import Random

from walsh_portfolio_audit import finite_formula, parity, spectrum


def round_table(numerators, denominator):
    size = len(numerators) // 2
    length = 2 * size
    inv_lambda = 1 << ((length.bit_length() + 1) // 2)
    base = inv_lambda * denominator
    signs = [
        [sense * (1 if parity(slope, col // 2) == col % 2 else -1)
         for col in range(length)]
        for slope in range(size) for sense in (1, -1)
    ]
    weights = [1] * len(signs)
    bits = []
    for col, num in enumerate(numerators):
        assert 0 <= num <= denominator
        drift = sum(w * sig[col] for w, sig in zip(weights, signs))
        bit = int(drift < 0)
        delta = denominator * bit - num
        updated = [w * (base + sig[col] * delta) for w, sig in zip(weights, signs)]
        assert min(updated) > 0 and sum(updated) <= base * sum(weights)
        weights = updated
        bits.append(bit)
    for sig in signs:
        discrepancy = abs(sum(sign * (denominator * bit - num)
                              for sign, bit, num in zip(sig, bits, numerators)))
        # ln(length) <= log2(length) and length is a power of two.
        assert discrepancy * inv_lambda <= (
            (length.bit_length()-1) * inv_lambda**2 + length
        ) * denominator
    return bits


def check_rounding():
    cases = 0
    for nums in product(range(5), repeat=4):
        round_table(nums, 4)
        cases += 1
    rng = Random(9277)
    for length in (2, 4, 8, 16, 32, 64):
        for _ in range(20):
            round_table([rng.randrange(257) for _ in range(length)], 256)
            cases += 1
    return cases


def toeplitz_values(width, depth):
    window = (1 << width) - 1
    for diagonals in range(1 << max(width + depth - 1, 0)):
        yield tuple(sum(parity((diagonals >> row) & window, x) << row
                        for row in range(depth)) for x in range(1 << width))


def admits_keys(members, outputs, budget):
    target = sum(1 << x for x in members)
    covers = set()
    for mapping in outputs:
        buckets = [mapping[x] for x in members]
        covers.add(sum(1 << x for x in members if buckets.count(mapping[x]) == 1))
    reached = {0}
    for _ in range(budget):
        reached = {old | new for old in reached for new in covers}
        if target in reached:
            return True
    return False


def check_hash_bounds():
    trials = 0
    for width in (1, 2, 3):
        all_maps = [list(toeplitz_values(width, d)) for d in range(width + 1)]
        for subset in range(1, 1 << (1 << width)):
            members = [x for x in range(1 << width) if subset >> x & 1]
            for budget in {width + 1, len(members).bit_length() + 1}:
                tests = [admits_keys(members, maps, budget) for maps in all_maps]
                assert sorted(tests) == tests and tests[-1]
                for d, works in enumerate(tests):
                    assert len(members) * 2 > (1 << d) or works
                    assert not works or len(members) <= budget * (1 << d)
                    trials += 1
    return trials


def count_extensions(clauses, var_count, pins):
    free = [i for i in range(1, var_count + 1) if i not in pins]
    total = 0
    for values in product((False, True), repeat=len(free)):
        assignment = pins | dict(zip(free, values))
        if all(any(assignment[abs(lit)] == (lit > 0) for lit in clause)
               for clause in clauses):
            total += 1
    return total


def check_native_shape():
    cnf, report_bits, public, pin = finite_formula(1, 1)
    formulas = 0
    for table in range(1 << len(report_bits)):
        scores = spectrum(table, 2)
        slope = min(range(2), key=lambda a: scores[a]**2)
        initial = {v: bool((table >> i) & 1) for i, v in enumerate(report_bits)}
        for x, tau in product(range(2), repeat=2):
            base = initial | {public[0]: bool(x)}
            counts = [count_extensions(cnf.clauses, cnf.n, base | {pin: tau ^ (1 - color)})
                      for color in (0, 1)]
            verdict = int(parity(slope, x) == tau)
            assert counts[verdict] == 1 and counts[1 - verdict] == 0
            assert all(count_extensions(cnf.clauses[:-2], cnf.n, base | {pin: bit}) == 1
                       for bit in (0, 1))
            formulas += 1
    return formulas


def check_local_counts():
    rng = Random(33091)
    families = 0
    for width in range(1, 7):
        for cost in range(width + 1):
            for _ in range(16):
                states = []
                for tag in range(rng.randrange(1, 12)):
                    # A tag is a disjunction of independent local certificates.
                    terms = []
                    for _ in range(rng.randrange(5)):
                        mask = sum(1 << i for i in rng.sample(range(width), cost))
                        terms.append((mask, rng.randrange(1 << width) & mask))
                    states.append((rng.randrange(2), terms))
                correct = []
                for x in range(1 << width):
                    kept = [color for color, terms in states
                            if any(x & mask == value for mask, value in terms)]
                    hits = sum(c == (x.bit_count() % 2) for c in kept)
                    correct.append(Fraction(hits, len(kept)) if kept else Fraction(1, 2))
                advantage = abs(sum(correct) / len(correct) - Fraction(1, 2))
                assert advantage <= Fraction(cost, width)
                assert min(correct) <= Fraction(width, 2 * width - cost)
                families += 1
    matched = 0
    for width in range(1, 10):
        for block in range(1, width+1):
            if width % block:
                continue
            groups = width // block
            for x in range(1 << width):
                addr = sum(parity(x, ((1 << block)-1) << (i * block)) << i
                           for i in range(groups))
                kept = [z for z in range(1 << groups) if (z ^ addr).bit_count() <= 1]
                correct = sum((1 ^ z.bit_count() % 2) == x.bit_count() % 2 for z in kept)
                assert Fraction(correct, len(kept)) == Fraction(width, width+block)
                matched += 1
    return families, matched


if __name__ == "__main__":
    print(f"{check_rounding()} rational forecast tables rounded against every Walsh slope")
    print(f"{check_hash_bounds()} Toeplitz isolation thresholds with full and entropy-based key lists")
    print(f"{check_native_shape()} finite pinned SAT labels checked by exhaustive primary-history counting")
    families, matched = check_local_counts()
    print(f"{families} locally certified postselection rules and {matched} sharp block predictions")
