"""Small exact checks for the competing-witness tests."""

from fractions import Fraction
from itertools import product
from math import comb


def entry(u, v, a, b):
    return 1 << (8 * u + 4 * v + 2 * a + b)


def check_support():
    questions = (0, 1)
    policies = list(product(questions, repeat=2))
    plays = [[sum(entry(u, v, left[u], right[v]) for u, v in policies)
              for left in policies] for right in policies]
    cell = [[sum(entry(u, v, a, b) for u, a in policies)
             for b in questions] for v in questions]
    positive = 0
    for table in range(1 << 16):
        no_perfect_refuter = all(any(table & play for play in row) for row in plays)
        question_exists = any(all(table & cell[v][b] for b in questions) for v in questions)
        assert no_perfect_refuter == question_exists
        positive += question_exists
    print(f"All 65,536 games checked, including {positive} with positive value")


def panel_value(types, samples):
    # Condition on the number of row draws sharing one chosen column type.
    value = Fraction(0)
    for hits in range(samples + 1):
        chance = Fraction(comb(samples, hits) * (types - 1)**(samples - hits), types**samples)
        minority = Fraction(sum(comb(hits, i) * min(i, hits - i)
                                for i in range(hits + 1)), 2**hits)
        value += chance * minority * Fraction(types, samples)
    return value


def check_panel():
    for types in (2, 4, 8, 16, 32):
        for samples in range(1, 17):
            value = panel_value(types, samples)
            assert value <= Fraction(samples - 1, 4 * types)
            assert value <= Fraction(1, 2)
    print("Checked 80 correlated-panel expectations against the finite bound")


def check_gate_slack():
    for h in range(1, 33):
        eta = Fraction(1, 3 * 2**h - 1)
        x = [(3 * 2**i - 2) * eta for i in range(h + 1)]
        copies = [value + eta for value in x[:-1]]
        slacks = [x[0], 1 - x[-1]]
        for parent, copy, successor in zip(x, copies, x[1:]):
            # A copy is AND(parent,1); its successor is OR(parent,copy).
            assert 0 <= parent <= 1 and 0 <= copy <= 1 and 0 <= successor <= 1
            slacks.extend([copy - parent, copy - 1, parent - copy,
                           parent - successor, copy - successor, successor - parent - copy])
        assert max(slacks) == eta
        assert 1 - eta == (3 * 2**h - 2) * eta
    print("Checked the rational assignments attaining the minimax slack at 32 depths")


if __name__ == "__main__":
    check_support()
    check_panel()
    check_gate_slack()
