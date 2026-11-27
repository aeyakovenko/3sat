"""Exhaustive short memory traces. Python 3, standard library only."""

from itertools import product


def bitonic_stages(length):
    """Yield (direction bit, partner mask) for each comparison stage."""
    assert length > 0 and length & (length - 1) == 0
    width = 2
    while width <= length:
        mask = width // 2
        while mask:
            yield width, mask
            mask //= 2
        width *= 2


def sort_network(rows):
    layer = list(rows)
    for direction, mask in bitonic_stages(len(rows)):
        for i in range(len(rows)):
            j = i ^ mask
            if i < j:
                ascending = i & direction == 0
                if (layer[i] > layer[j]) == ascending:
                    layer[i], layer[j] = layer[j], layer[i]
    return layer


def sequentially_valid(trace):
    memory = {}
    for address, write, value in trace:
        if write:
            memory[address] = value
        elif memory.get(address, 0) != value:
            return False
    return True


def check_sorted(trace):
    rows = [(address, time, write, value)
            for time, (address, write, value) in enumerate(trace)]
    ordered = sort_network(rows)
    assert ordered == sorted(rows)
    previous_address, previous_value = None, 0
    for address, _, write, value in ordered:
        expected = previous_value if previous_address == address else 0
        if not write and expected != value:
            return False
        previous_address, previous_value = address, value
    return True


def check_block_partners():
    cases = 0
    for log_length in range(1, 9):
        size = 1 << log_length
        for low_bits in range(log_length + 1):
            block_size = 1 << low_bits
            for _, mask in bitonic_stages(size):
                for start in range(0, size, block_size):
                    partners = {(i ^ mask) >> low_bits
                                for i in range(start, start + block_size)}
                    assert partners == {(start >> low_bits) ^ (mask >> low_bits)}
                    cases += 1
    return cases


if __name__ == "__main__":
    events = list(product(range(2), (False, True), range(2)))
    valid, total = 0, 0
    for length in (1, 2, 4):
        for trace in product(events, repeat=length):
            expected = sequentially_valid(trace)
            assert check_sorted(trace) == expected
            valid += expected
            total += 1
    print(f"Replay and sorted checks agree on {total} traces ({valid} valid).")
    print(f"Verified {check_block_partners()} stage/block partner cases.")
