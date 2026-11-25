"""Finite checks of the local sorts, canonical stack and gap witnesses."""

from bisect import bisect_left
from functools import lru_cache
from itertools import permutations, product


def deletion_distance(sequence):
    ends = []
    for key in sequence:
        index = bisect_left(ends, key)
        if index == len(ends):
            ends.append(key)
        else:
            ends[index] = key
    return len(sequence) - len(ends)


def two_sorts(sequence, block):
    length = len(sequence)
    padded = list(sequence)
    padded.extend(range(length, length + (-length) % (2 * block)))
    for start in (0, block):
        for i in range(start, len(padded) - block, 2 * block):
            padded[i:i + 2 * block] = sorted(padded[i:i + 2 * block])
    assert padded[length:] == list(range(length, len(padded)))
    return tuple(padded[:length])


def minimum_long_cover(sequence, block):
    edges = [(i, j) for i, left in enumerate(sequence)
             for j in range(i + block + 1, len(sequence)) if left > sequence[j]]

    @lru_cache(None)
    def search(active):
        edge = next(((i, j) for i, j in edges if active >> i & active >> j & 1), None)
        if edge is None:
            return 0
        return 1 + min(search(active ^ (1 << k)) for k in edge)

    return search((1 << len(sequence)) - 1)


def check_sort_bound():
    cases = 0
    for size in range(1, 8):
        for seq in permutations(range(size)):
            for block in range(1, size + 1):
                cover = minimum_long_cover(seq, block)
                distance = deletion_distance(two_sorts(seq, block))
                assert distance <= 2 * cover, (seq, block, cover, distance)
                cases += 1
    sharp = (1, 3, 2, 0)
    assert minimum_long_cover(sharp, 1) == 1
    assert deletion_distance(two_sorts(sharp, 1)) == 2
    return cases


def real_stack(sequence):
    stack = []
    restores = []
    opens = set()
    for i, value in enumerate(sequence):
        if stack and sequence[stack[-1]] > value:
            opens.add(stack.pop())
            restores.append(stack[-1] if stack else -1)
        else:
            stack.append(i)
    return tuple(stack), tuple(sorted(opens)), tuple(restores)


def certified_stacks(sequence):
    """Enumerate every structurally legal push flag and predecessor guess."""
    size = len(sequence)

    def visit(i, top, opens, pops, kept):
        if i == size:
            if sorted(opens) == sorted(pops):
                yield tuple(kept), tuple(sorted(j for j, _ in opens)), tuple(t for _, t in pops)
            return
        if top >= 0 and sequence[top] > sequence[i]:
            # Guess any real index or the empty sentinel, even a future/self index.
            for restored in range(-1, size):
                yield from visit(i + 1, restored, opens, pops + [(top, restored)], kept)
        else:
            yield from visit(i + 1, i, opens, pops, kept + [i])
            yield from visit(i + 1, i, opens + [(i, top)], pops, kept)

    yield from visit(0, -1, [], [], [])


def check_unique():
    stack_cases = gap_guesses = 0
    for size in range(1, 6):
        for sequence in permutations(range(size)):
            expected = real_stack(sequence)
            assert list(certified_stacks(sequence)) == [expected]
            kept, _, pops = expected
            assert len(pops) <= deletion_distance(sequence)
            discarded = sorted(set(range(size)) - set(kept))
            ordered = []
            for labels in product((-1, *kept), repeat=len(discarded)):
                gaps = {gap: [] for gap in (-1, *kept)}
                for pos, gap in zip(discarded, labels):
                    gaps[gap].append(sequence[pos])
                output = sorted(gaps[-1])
                for pos in kept:
                    output.append(sequence[pos])
                    output.extend(sorted(gaps[pos]))
                if output == list(range(size)):
                    ordered.append(labels)
                gap_guesses += 1
            assert len(ordered) == 1
            stack_cases += 1
    return stack_cases, gap_guesses


if __name__ == '__main__':
    print(f'{check_sort_bound()} permutation/block-width tests against exact minimum covers')
    stacks, gaps = check_unique()
    print(f'{stacks} unique stack certificates; {gaps} candidate insertions checked')
