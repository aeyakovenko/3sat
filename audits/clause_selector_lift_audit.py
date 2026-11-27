"""Test the one-slot induction on explicit proper 3-CNFs and the packed scanner."""
from itertools import product
from small_sat_ram_clocks import BASE, HEADER

FILL = (4 << 11) | (5 << 7) | (6 << 3)


def encoded_catalogue(slot_types, enabled):
    return [HEADER] + [BASE | p if x else FILL for p, x in zip(slot_types, enabled)]


def satisfying_assignment(records):
    # Direct Boolean semantics over all six variable names. The three bits of p
    # index the falsifying assignment in the same order as the three names.
    for a in range(64):
        for rec in records[1:]:
            names = [(rec >> s) & 15 for s in (11, 7, 3)]
            value = sum(((a >> (name - 1)) & 1) << j for j, name in enumerate(names))
            if (rec & 7) == value:
                break
        else:
            return True
    return False


def packed_scan(records, width):
    assert width % 16 == 0 and records[0] == HEADER
    lanes = width // 16
    low = sum(1 << (16 * i) for i in range(lanes))
    universe = (1 << width) - 1
    patterns = [BASE | p for p in range(8)] + [FILL]
    present = 0
    for start in range(0, len(records), lanes):
        part = records[start:start + lanes]
        active = sum(1 << (16 * i) for i in range(len(part)) if start + i > 0)
        word = sum(record << (16 * j) for j, record in enumerate(part))
        legal = 0
        for p, record in enumerate(patterns):
            diff = word ^ (record * low)
            for shift in (8, 4, 2, 1):
                diff |= diff >> shift
            matched = (~diff & universe) & active
            legal |= matched
            if p < 8 and matched:
                present |= 1 << p
        if legal != active:
            return None
    return present != 255


def check():
    truth = {}
    for enabled in product((False, True), repeat=8):
        records = encoded_catalogue(range(8), enabled)
        result = satisfying_assignment(records)
        assert result == (not all(enabled))
        truth[enabled] = result
    checked = 0
    for extras in range(6):
        # Duplicate the type-0 clause, once per induction step.
        slots = [0] * (1 + extras) + list(range(1, 8))
        parity = False
        for enabled in product((False, True), repeat=len(slots)):
            original = (any(enabled[:extras + 1]),) + enabled[extras + 1:]
            result = truth[original]
            records = encoded_catalogue(slots, enabled)
            for width in (16, 32, 48, 64, 112):
                assert packed_scan(records, width) == result
            parity ^= result
            checked += 1
        assert parity
    assert packed_scan([HEADER, FILL ^ 128], 48) is None
    print(f'{checked:,} selector masks, five word widths, direct six-variable base truth table')


if __name__ == '__main__':
    check()
