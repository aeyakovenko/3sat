"""Finite checks for public-tape replacement in a PCP verifier simulation."""

from fractions import Fraction
from itertools import product


def leaves(addresses, tape, depth):
    """Tree nodes are in heap order. Repeated or data-dependent reads are allowed."""
    node = 0
    for _ in range(depth):
        reply = (tape >> addresses[node]) & 1
        node = 2 * node + 1 + reply
    return node - ((1 << depth) - 1)


def check_all_depth_three_trees():
    # Uniform even-parity tapes on four positions are three-wise independent.
    width = 4
    depth = 3
    even = [tape for tape in range(1 << width) if tape.bit_count() % 2 == 0]
    odd = [tape for tape in range(1 << width) if tape.bit_count() % 2 == 1]
    branches = (1 << depth) - 1
    count = 0
    for addresses in product(range(width), repeat=branches):
        # Identical distributions on reached leaves cover all leaf predicates,
        # fixed auxiliary advice, verifier coins, and optional early stops.
        balance = [0] * (1 << depth)
        for tape in even:
            balance[leaves(addresses, tape, depth)] += 1
        for tape in odd:
            balance[leaves(addresses, tape, depth)] -= 1
        assert balance == [0] * (1 << depth)
        count += 1
    return count


def event_rate(tapes, test):
    return Fraction(sum(test(tape) for tape in tapes), len(tapes))


def check_changes_outside_the_transcript():
    tapes = list(range(16))
    even = [tape for tape in tapes if tape.bit_count() % 2 == 0]
    odd = [tape for tape in tapes if tape.bit_count() % 2 == 1]

    # Advice received after the tape can select a coordinate that equals one.
    # Each fixed advice observes one bit, whereas their union can observe four.
    for address in range(4):
        def selected_bit(tape):
            return (tape >> address) & 1

        assert event_rate(tapes, selected_bit) == event_rate(even, selected_bit) == Fraction(1, 2)
    any_advice = (event_rate(tapes, bool), event_rate(even, bool))
    assert any_advice == (Fraction(15, 16), Fraction(7, 8))

    # The actual one-variable 3-CNF (x ∨ x ∨ x) has projected witness {1}.
    # At level two, its affine Toeplitz hash maps x=1 to diagonals XOR offset.
    # The original projected assignment survives precisely when these pairs agree.
    def isolates(tape):
        diagonals, offset = tape & 3, tape >> 2
        return diagonals == offset

    isolation = tuple(event_rate(source, isolates) for source in (tapes, even, odd))
    assert isolation == (Fraction(1, 4), Fraction(1, 2), 0)
    return any_advice, isolation


if __name__ == '__main__':
    count = check_all_depth_three_trees()
    advice, isolation = check_changes_outside_the_transcript()
    print(f'{count} adaptive depth-three trees have identical transcript distributions')
    print(f'Existential advice success under uniform and even tapes: {advice[0]}, {advice[1]}')
    print(f'Isolation under uniform, even, and odd tapes: {isolation[0]}, {isolation[1]}, {isolation[2]}')
