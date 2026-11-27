"""Exhaustive small checks for the paired-name decoder and adaptive probe bound."""

from collections import Counter
from functools import cache


def hidden_position(name: int, length: int) -> tuple[int, int]:
    """Use low-order bits for the first positions of an experimental name."""
    capacity = (length + 1) // 2
    block_size = 1 << (capacity.bit_length() - 1)
    address = 0
    for column in range(1, block_size):
        if (name >> (column - 1)) & 1:
            address ^= column
    return block_size, block_size - 1 + address


def delete_at(name: int, position: int) -> int:
    prefix = name & ((1 << position) - 1)
    suffix = name >> (position + 1)
    return prefix | (suffix << position)


def check_decoder(length: int) -> int:
    counts = Counter()
    for name in range(1 << length):
        _, position = hidden_position(name, length)
        mate = name ^ (1 << position)
        assert hidden_position(mate, length)[1] == position
        decoded = delete_at(name, position)
        assert delete_at(mate, position) == decoded
        counts[decoded] += 1
    assert counts == {original: 2 for original in range(1 << (length - 1))}
    return len(counts)


def optimal_probes(block_size: int) -> tuple[list[int], int]:
    length = 2 * block_size - 1
    pairs = []
    for name in range(1 << length):
        block, position = hidden_position(name, length)
        assert block == block_size
        mate = name ^ (1 << position)
        if name < mate:
            pairs.append((name, mate))

    @cache
    def best(mask: int, bits: int, remaining: int) -> int:
        inside = [(x, y) for x, y in pairs if x & mask == y & mask == bits]
        if not inside or remaining == 0:
            return 0
        if remaining >= length - mask.bit_count():
            return len(inside)
        answer = 0
        for position in range(length):
            bit = 1 << position
            if bit & mask:
                continue
            separated = sum(bool((x ^ y) & bit) for x, y in inside)
            left = best(mask | bit, bits, remaining - 1)
            right = best(mask | bit, bits | bit, remaining - 1)
            answer = max(answer, separated + left + right)
        return answer

    optimum = [best(0, 0, depth) for depth in range(length + 1)]
    for depth, count in enumerate(optimum):
        queried = min(depth, block_size)
        data_mask = ((1 << queried) - 1) << (block_size - 1)
        parity_hits = sum(((x ^ y) & data_mask).bit_count() % 2 for x, y in pairs)
        assert count == parity_hits == queried * len(pairs) // block_size
    return optimum, best.cache_info().currsize


if __name__ == "__main__":
    total_pairs = sum(check_decoder(length) for length in range(1, 11))
    print(f"Lengths 1 through 10 verified {total_pairs} decoded pairs.")
    for block_size in (2, 4):
        optimum, states = optimal_probes(block_size)
        print(f"B={block_size}, adaptive optimum by depth {optimum}, {states} states.")
