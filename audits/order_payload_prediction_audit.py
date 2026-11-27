"""Check adaptive payload reconstruction and the order code for a predictable tail."""

from itertools import permutations, product
from random import Random

from word_permutation_history_audit import encode_clause, path_clauses, tautology, unit


class Presentation:
    """Public word adapter. No table values or physical permutation are stored here."""

    def __init__(self, count, sign):
        self.count = count
        width = max(5, (4 * count + 3).bit_length() + 1)
        self.word_bits = 12 * width
        base = 1 << (width - 2)
        guard = encode_clause(tautology(base - 1), width)
        phase = width + 1
        logical = [unit(1)] * count if sign else path_clauses(count)
        self.prefixes = [
            guard[phase:] + encode_clause(clause, width)
            + encode_clause(tautology(base + index), width)
            for index, clause in enumerate(logical)
        ]
        self.suffixes = [
            encode_clause(tautology(base + count + value), width) + guard[:phase]
            for value in range(count)
        ]

    def movable_word(self, pair):
        label, value = pair
        return int(self.prefixes[label] + self.suffixes[value], 2)

    def fixed_word(self, address):
        assert address in (0, self.count + 1)
        return (0x35D2 + address) % (1 << self.word_bits)


def run_monitor(count, read):
    """Both fixed-word and adaptive repeated loads influence later discoveries."""
    unread = list(range(1, count + 1))
    visited = []
    state = read(0)
    while unread:
        state ^= read(count + 1)
        if visited:
            state ^= read(visited[state % len(visited)])
        address = unread.pop(state % len(unread))
        result = read(address)
        visited.append(address)
        state = (state << 1) ^ result ^ (result >> 9)
    return visited


def predict(count, address, feedback, prior):
    used = {label for label, _ in prior}
    unused = [label for label in range(count) if label not in used]
    index = (feedback + address + len(prior)) % len(unused)
    last = prior[-1][1] if prior else 0
    return unused[index], (feedback + address + last) % count


def run_with_corrections(layout, supply_pair):
    count = layout.count
    cache = {}
    discoveries = []
    table = {}
    feedback = 0

    def read(address):
        nonlocal feedback
        if address in (0, count + 1):
            word = layout.fixed_word(address)
        else:
            if address not in cache:
                predicted = predict(count, address, feedback, discoveries)
                pair = supply_pair(len(discoveries), address, predicted)
                label, value = pair
                assert 0 <= label < count and 0 <= value < count
                assert label not in table
                table[label] = value
                discoveries.append(pair)
                cache[address] = layout.movable_word(pair)
            word = cache[address]
        feedback = ((feedback * 19) ^ word ^ (word >> 5) ^ address) % 65521
        return word

    order = run_monitor(count, read)
    assert len(table) == count
    return tuple(table[i] for i in range(count)), order


def encode_exceptions(layout, order, values):
    exceptions = {}

    def observed(ordinal, address, predicted):
        label = order[address - 1]
        pair = (label, values[label])
        if predicted != pair:
            exceptions[ordinal] = pair
        return pair

    recovered, addresses = run_with_corrections(layout, observed)
    assert recovered == values
    return exceptions, addresses


def decode_exceptions(layout, exceptions):
    def corrected(ordinal, _address, predicted):
        return exceptions.get(ordinal, predicted)

    return run_with_corrections(layout, corrected)


def check_discoveries():
    tested = 0
    for count in (2, 3, 4):
        for sign in (False, True):
            layout = Presentation(count, sign)
            for values in product(range(count), repeat=count):
                for order in permutations(range(count)):
                    exceptions, addresses = encode_exceptions(layout, order, values)
                    decoded, replayed_addresses = decode_exceptions(layout, exceptions)
                    assert decoded == values
                    assert replayed_addresses == addresses
                    tested += 1
    return tested


def split_size(count):
    """Smallest h for which ranks of h front labels carry all tail values."""
    size = (count - 1).bit_length()
    capacity = 0
    for front in range(count + 1):
        if capacity >= (count - front) * size:
            return front
        capacity += (front + 1).bit_length() - 1
    raise AssertionError("all-front split must fit")


def encode_front(front, values, size):
    """Each rank reads at most one more size-bit payload word; pad with zeros."""
    active = list(range(front))
    source = iter(values)
    buffer = 0
    buffered = 0
    for remaining in range(front, 0, -1):
        width = remaining.bit_length() - 1
        if buffered < width:
            buffer |= next(source, 0) << buffered
            buffered += size
        assert 0 <= width <= buffered <= 2 * size
        rank = buffer & ((1 << width) - 1)
        buffer >>= width
        buffered -= width
        label = active[rank]
        active[rank] = active[remaining - 1]
        yield label


def decode_front(labels, front, tail, size):
    """One swap, one inverse update and at most one emitted word per label."""
    active = list(range(front))
    position = list(range(front))
    buffer = 0
    buffered = 0
    values = []
    for step, label in enumerate(labels):
        remaining = front - step
        assert 0 <= label < front
        rank = position[label]
        width = remaining.bit_length() - 1
        assert 0 <= rank < 1 << width
        last = active[remaining - 1]
        active[rank] = last
        position[last] = rank
        position[label] = -1
        buffer |= rank << buffered
        buffered += width
        assert buffered <= 2 * size
        if size and buffered >= size:
            if len(values) < tail:
                values.append(buffer & ((1 << size) - 1))
            buffer >>= size
            buffered -= size
    assert len(labels) == front
    if not size:
        assert tail <= 1
        return [0] * tail
    assert len(values) == tail
    return values


def check_tail_case(count, front, table):
    size = (count - 1).bit_length()
    tail = count - front
    front_order = list(encode_front(front, table[front:], size))
    assert sorted(front_order) == list(range(front))
    # The predictor learns the physical prefix as feedback, with no access to the table.
    physical = [(label, table[label]) for label in [*front_order, *range(front, count)]]
    observed_labels = [label for label, _ in physical[:front]]
    recovered = decode_front(observed_labels, front, tail, size)
    predicted = [(front + j, value) for j, value in enumerate(recovered)]
    assert predicted == physical[front:]


def check_tail_codes():
    rng = Random(20261124)
    counts = [*range(1, 14), 15, 16, 17, 31, 32, 33, 63, 64, 65,
              127, 128, 129, 257, 1023, 1024, 1025, 4096, 4097]
    cases = 0
    for count in counts:
        size = (count - 1).bit_length()
        minimum = split_size(count)
        # Also test surplus capacity, including an empty tail.
        for front in sorted({minimum, min(count, minimum + 1), count}):
            tail = count - front
            capacity = sum(j.bit_length() - 1 for j in range(1, front + 1))
            assert capacity >= tail * size
            if front == minimum and front:
                assert capacity - (front.bit_length() - 1) < (tail + 1) * size
            if count <= 13 and count ** tail <= 5000:
                tails = product(range(count), repeat=tail)
            else:
                tails = ([rng.randrange(count) for _ in range(tail)] for _ in range(3))
            for payload in tails:
                table = [rng.randrange(count) for _ in range(front)] + list(payload)
                check_tail_case(count, front, table)
                cases += 1
    return len(counts), cases


if __name__ == "__main__":
    print(f"{check_discoveries():,} adaptive table/order/sign replays passed")
    sizes, cases = check_tail_codes()
    print(f"{cases:,} permutation rank-stream cases across {sizes} alphabet sizes passed")
