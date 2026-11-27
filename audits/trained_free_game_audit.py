"""Exhaust finite examples for the trained-strategy and independent-panel bounds."""

from fractions import Fraction
from itertools import combinations_with_replacement, product


def row_statistics(row):
    # A row has two Alice labels, two Bob questions and two Bob labels.
    def payoff(alice, y, bob):
        return (row >> (4 * alice + 2 * y + bob)) & 1

    left_best = []
    for policy in range(4):
        left_best.append(max(sum(payoff(a, y, (policy >> y) & 1) for y in range(2))
                             for a in range(2)))
    differences = [tuple(payoff(a, y, 1) - payoff(a, y, 0) for y in range(2))
                   for a in range(2)]
    return left_best, differences


def induced(first, second):
    return int(first > 0) + 2 * int(second > 0)


def binary_games():
    stats = [row_statistics(row) for row in range(256)]
    one_example_insufficient = 0
    for (left, left_samples), (right, right_samples) in product(stats, repeat=2):
        scores = [a + b for a, b in zip(left, right)]
        optimum = max(scores)
        training = left_samples + right_samples
        score_one = max(scores[induced(x, y)] for x, y in training)
        score_two = max(scores[induced(x + u, y + v)]
                        for (x, y), (u, v) in combinations_with_replacement(training, 2))
        assert score_one <= score_two == optimum
        one_example_insufficient += int(score_one < optimum)
    assert one_example_insufficient
    return 256**2, one_example_insufficient


def parity(value):
    return value.bit_count() % 2


def simplex_game():
    # The all-ones logical word and the [7,3,4] binary simplex stabilizer.
    rows = range(1, 8)
    message_code = [sum(parity(i & m) << i for i in range(8)) for m in range(8)]
    violated = [sum(parity(i & m) != 1 for i in rows) for m in range(8)]
    assert min(violated) == 3
    agreements = [[max(8 - (word ^ message_code[m]).bit_count()
                       for m in range(8) if parity(i & m) == 1)
                   for i in rows] for word in range(256)]
    smallest_conflict = 8
    for subset in range(1, 1 << 7):
        selected = [i for i in rows if subset & (1 << (i-1))]
        consistent = any(all(parity(i & m) for i in selected) for m in range(8))
        optimum = max(sum(table[i-1] for i in selected) for table in agreements)
        assert (optimum == len(selected) * 8) == consistent
        if not consistent:
            smallest_conflict = min(smallest_conflict, len(selected))
    full = Fraction(max(map(sum, agreements)), 7*8)
    assert smallest_conflict == 3
    assert full <= 1 - Fraction(3, 7) * Fraction(1, 4)
    return min(violated), smallest_conflict, full


def translated_good_events():
    # With eight seeds and two shifts the two counting bounds apply at 7 and 2.
    high = low = 0
    for event in range(256):
        if 2 < event.bit_count() < 7:
            continue
        all_have_offset = all(any(event & (1 << (u ^ x)) and event & (1 << (u ^ y))
                                  for u in range(8))
                              for x, y in product(range(8), repeat=2))
        assert all_have_offset == (event.bit_count() >= 7)
        high += all_have_offset
        low += not all_have_offset
    return high, low


if __name__ == "__main__":
    print("Binary games (all, one example insufficient):", binary_games())
    print("Simplex game (minimum failed rows, minimum conflict, value):", simplex_game())
    print("Translated events (all shifts succeed, some shift pair fails):", translated_good_events())
