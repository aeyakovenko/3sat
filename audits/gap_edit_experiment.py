"""Finite tests for gap-edit-watchdogs.md. Run with Python 3.10 or newer."""

from collections import Counter
from itertools import combinations, product


def multiply(left: int, right: int) -> int:
    """Multiply in F_8 with modulus X^3 + X + 1."""
    result = 0
    while right:
        if right & 1:
            result ^= left
        right >>= 1
        left <<= 1
        if left & 8:
            left ^= 0b1011
    return result


def encode(message: tuple[int, ...]) -> tuple[int, ...]:
    bits = []
    a, b, c, d = message
    for x, y in product(range(8), repeat=2):
        value = a ^ multiply(b, x) ^ multiply(c, y) ^ multiply(d, multiply(x, y))
        bits.extend((value & mask).bit_count() % 2 for mask in range(8))
    return tuple(bits)


def check_code() -> None:
    words = [encode(message) for message in product(range(2), repeat=4)]
    length = len(words[0])
    distance = min(sum(x != y for x, y in zip(left, right))
                   for left, right in combinations(words, 2))
    assert length == 512 and distance == 196
    assert 8 * distance >= 3 * length
    print(f"16 codewords of {length} bits, minimum distance {distance}")


def check_edit_stream() -> None:
    # Clause j is the unique width-3 clause falsified by assignment j.
    states = [i ^ (i >> 1) for i in range(8)]
    assert all((a ^ b).bit_count() == 1 for a, b in zip(states, states[1:]))
    for watched_mask in range(256):
        watched = [j for j in range(8) if watched_mask & (1 << j)]
        slots = {j: [0] * 3 for j in watched}
        current = 0
        detected = []
        for mark in states:
            for v in range(3):
                if (current ^ mark) & (1 << v):
                    for values in slots.values():
                        values[v] ^= 1
            detected.append(any(all(bit == (j >> v) & 1 for v, bit in enumerate(values))
                                for j, values in slots.items()))
            current = mark
        assert detected == [j in watched for j in states]
        assert all(detected) == (watched_mask == 255)

    # Count ordered lists with replacement by their union, without enumerating 8^16 lists.
    lists = Counter({0: 1})
    for _ in range(16):
        next_lists = Counter()
        for mask, count in lists.items():
            for j in range(8):
                next_lists[mask | (1 << j)] += count
        lists = next_lists
    assert sum(lists.values()) == 8**16
    assert 0 < 8**16 - 8 * 7**16 <= lists[255]
    print(f"All eight marks are caught by {lists[255]} of the {8**16} ordered lists.")


if __name__ == "__main__":
    check_code()
    check_edit_stream()
