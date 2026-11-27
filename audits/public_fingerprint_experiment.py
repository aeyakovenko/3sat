"""Exact finite product tests for a stamped twelve-cell write/read RAM."""

from itertools import combinations


CELLS = 12
PRIME = 53
WORDS = 1 << CELLS
POINTS = range(PRIME)
# Start outside the assigned tags; all possible points are tried if needed.
SEARCH_ORDER = tuple(range(4 * CELLS, PRIME)) + tuple(range(4 * CELLS))


def product_table(point, offset):
    """Products for all vectors, with bit i selecting tag 4*i + offset + bit."""
    products = [1]
    for cell in range(CELLS):
        zero_factor = point - (4 * cell + offset)
        products = [v * zero_factor % PRIME for v in products] + [
            v * (zero_factor - 1) % PRIME for v in products
        ]
    return products


def full_product(point, write_word, read_word, address_order):
    """Independently form the actual records and scan their product."""
    result = 1
    for cell in address_order:
        write_bit = (write_word >> cell) & 1
        read_bit = (read_word >> cell) & 1
        for tag in (4 * cell + 2 + write_bit, 4 * cell + read_bit):
            result = result * (point - tag) % PRIME
    return result


def generate_payoffs():
    chron = []
    memory = []
    singleton_inputs = set()
    for point in POINTS:
        reads = product_table(point, 0)
        writes = product_table(point, 2)
        bins = [[] for _ in POINTS]
        for word, digest in enumerate(reads):
            bins[digest].append(word)
        singleton_inputs.update(bucket[0] for bucket in bins if len(bucket) == 1)
        # One false chronological log for the same fixed zero input at each point.
        false_read = next(v for v in bins[reads[0]] if v != 0)
        assert full_product(point, 0, false_read, reversed(range(CELLS))) == full_product(
            point, 0, 0, range(CELLS)
        )
        # Chronological writes are fixed by input zero; read word zero is excluded later.
        chron.append([writes[0] * value % PRIME for value in reads])
        # Locally valid memory views may choose any write word but must read it back.
        memory.append([writes[word] * reads[word] % PRIME for word in range(WORDS)])
    assert not singleton_inputs
    return chron, memory


def matching_buckets(point, left, right, chron, memory):
    left_bins = [[] for _ in POINTS]
    right_bins = [[] for _ in POINTS]
    for word in left:
        left_bins[chron[point][word]].append(word)
    for word in right:
        right_bins[memory[point][word]].append(word)
    return [(a, b) for a, b in zip(left_bins, right_bins) if a and b]


def winning_point(left, right, remaining, chron, memory):
    """Return a first move whose every common numerical reply is refutable."""
    if remaining == 1:
        for point in SEARCH_ORDER:
            values = {chron[point][word] for word in left}
            if all(memory[point][word] not in values for word in right):
                return point
        return None
    for point in SEARCH_ORDER:
        branches = matching_buckets(point, left, right, chron, memory)
        branches.sort(key=lambda b: len(b[0]) * len(b[1]), reverse=True)
        if all(winning_point(a, b, remaining - 1, chron, memory) is not None
               for a, b in branches):
            return point
    return None


def count_nonseparating_triples(left, right, chron, memory):
    """Count a triple when one false pair has equal products at all its points."""
    witnessed = 0
    for first, second in combinations(POINTS, 2):
        unproved = set(range(second + 1, PRIME))
        if not unproved:
            continue
        first_left = chron[first]
        second_left = chron[second]
        first_right = memory[first]
        second_right = memory[second]
        left_bins = {}
        right_bins = {}
        for word in left:
            key = first_left[word] * PRIME + second_left[word]
            left_bins.setdefault(key, []).append(word)
        for word in right:
            key = first_right[word] * PRIME + second_right[word]
            right_bins.setdefault(key, []).append(word)
        for key, candidates in left_bins.items():
            bank = right_bins.get(key)
            if bank is None:
                continue
            for third in tuple(unproved):
                values = {chron[third][word] for word in candidates}
                if any(memory[third][word] in values for word in bank):
                    unproved.remove(third)
            if not unproved:
                break
        witnessed += PRIME - second - 1 - len(unproved)
    return witnessed


def main():
    assert 4 * CELLS <= PRIME
    chron, memory = generate_payoffs()
    left = range(1, WORDS)
    right = range(WORDS)
    assert winning_point(left, right, 2, chron, memory) is None
    first = winning_point(left, right, 3, chron, memory)
    assert first == 48
    nonseparating = count_nonseparating_triples(left, right, chron, memory)
    assert nonseparating == PRIME * (PRIME - 1) * (PRIME - 2) // 6
    print(f'All {WORDS} inputs have a read collision at each of {PRIME} points.')
    print(f'Fixed zero input: all {nonseparating:,} fixed triples admit a false log pair.')
    print(f'No two-round adaptive policy separates; three rounds suffice, starting at {first}.')


if __name__ == '__main__':
    main()
