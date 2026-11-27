"""Finite checks of native transcript cycles, valuation, and a guest memory chart."""
from itertools import product


def valuation(number):
    return (number & -number).bit_length() - 1


def check_leaf_dimensions():
    checked = 0
    for dimensions in product(range(6), repeat=5):
        accepted = sum(1 << d for d in dimensions)
        assert min(dimensions) <= valuation(accepted)
        checked += 1
    return checked


def check_cycle_potentials():
    checked = 0
    for length in range(1, 8):
        for label, potential in product(range(1 << length), repeat=2):
            rotated = (potential >> 1) | ((potential & 1) << (length - 1))
            defects = label ^ potential ^ rotated
            assert label.bit_count() % 2 == defects.bit_count() % 2
            checked += 1
    return checked


def check_unique_records():
    checked = 0
    for step_count in range(1, 5):
        for control, flip, pin in product(range(2), repeat=3):
            def accepts(record):
                value = control
                for t in range(step_count):
                    value ^= flip ^ (t & 1)
                    if (record >> t) & 1 != value:
                        return False
                return value == pin

            records = [y for y in range(1 << step_count) if accepts(y)]
            expected = control
            for i in range(step_count):
                expected ^= flip ^ (i & 1)
            assert len(records) == int(expected == pin)
            checked += 1
    return checked


def check_memory_chart():
    checked = 0
    for width in range(3, 11):
        modulus = 1 << width
        inverse = pow(3, -1, modulus)
        memory = [0] * modulus
        for iterations in range(modulus // 2):
            for address, actual in enumerate(memory):
                earlier = inverse * (address - 5) % modulus
                decoded = 2 * earlier + 1 if earlier < iterations else 0
                assert decoded == actual
                checked += 1
            address = (3 * iterations + 5) % modulus
            memory[address] = 2 * iterations + 1
    return checked


def advance(pulses, retired, lower):
    live = pulses & ~retired & ~((1 << lower) - 1)
    selected = live & -live
    return selected, retired | selected


def check_truncated_forecasts():
    checked = 0
    for table in product(range(8), repeat=4):
        truthful_states = [0]
        winners = []
        for pulses in table:
            won, new_state = advance(pulses, truthful_states[-1], 0)
            winners.append(won)
            truthful_states.append(new_state)
        for limits, windows in [((1, 1, 2, 2), (1, 1, 1, 2)),
                                ((0, 1, 1, 2), (1, 2, 2, 3)),
                                ((1, 1, 1, 1), (1, 1, 2, 2))]:
            mistakes = 0
            for end, (limit, width) in enumerate(zip(limits, windows), start=1):
                left = max(0, end - width)
                state = truthful_states[left]
                for pulses in table[left:end]:
                    won, state = advance(pulses, state, limit)
                mismatch = (winners[end - 1], truthful_states[end]) != (won, state)
                if mismatch:
                    assert any(w & ((1 << limit) - 1) for w in winners[left:end])
                    mistakes += 1
                assert mistakes <= limit * width
                checked += 1
    return checked


if __name__ == "__main__":
    leaves = check_leaf_dimensions()
    cycles = check_cycle_potentials()
    records = check_unique_records()
    reads = check_memory_chart()
    windows = check_truncated_forecasts()
    print(f"Verified {leaves} leaf valuations, {cycles} cycle gauges, "
          f"{records} deterministic transcript pins, {reads} guest word reads and {windows} truncated forecasts.")
