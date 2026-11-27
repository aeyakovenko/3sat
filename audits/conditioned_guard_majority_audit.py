"""Check the conditioned guard on length-four affine tables over F_8."""

from itertools import combinations, product


def field_product(first, second):
    result = 0
    while second:
        if second & 1:
            result ^= first
        first <<= 1
        if first & 8:
            first ^= 11  # T³ + T + 1
        second >>= 1
    return result


def unpack(table):
    return [(table >> (3 * position)) & 7 for position in range(4)]


def message_from_last_two(first, second):
    slope = first ^ second  # 2 + 3 = 1 in F_8.
    intercept = first ^ field_product(2, slope)
    return intercept | (slope << 3)


def check_coefficients(code, distances):
    radius = 2
    available = next(
        table for table in range(1 << 6)
        if table.bit_count() == distances[table] == 4
    )
    slots = [1 << bit for bit in range(6) if available & (1 << bit)]
    count = 0
    for linear_mask in range(64):
        for center in code:
            first, second = unpack(center)[2:]
            first_bit = ((linear_mask & message_from_last_two(first, 0)).bit_count() % 2)
            second_bit = ((linear_mask & message_from_last_two(0, second)).bit_count() % 2)
            found_weight = None
            for threshold in range(3):
                noise = first_bit * slots[0] + second_bit * slots[1]
                noise += sum(slots[2 : 2 + radius - threshold])
                is_near = distances[center ^ noise] <= radius
                assert is_near == (first_bit + second_bit <= threshold)
                if is_near and found_weight is None:
                    found_weight = threshold
                count += 1
            actual = (linear_mask & message_from_last_two(first, second)).bit_count() % 2
            assert found_weight is not None and found_weight % 2 == actual
    return count


def main():
    code = {
        sum((a ^ field_product(b, pos)) << (3 * pos) for pos in range(4))
        for a, b in product(range(8), repeat=2)
    }
    distances = [min((table ^ c).bit_count() for c in code) for table in range(4096)]
    radius = 1
    mask = next(
        table for table in range(4096)
        if table.bit_count() == distances[table] == 2 * radius + 1
    )
    pairs = list(combinations(range(8), 2))
    marginals = {pair: [0] * 64 for pair in pairs}
    count = 0
    for center, aux in product(code, range(4096)):
        noise = aux & mask
        first = aux
        second = aux ^ center ^ noise
        assert (distances[first ^ second] <= radius) == (noise.bit_count() <= radius)
        symbols = unpack(first) + unpack(second)
        for i, j in pairs:
            marginals[i, j][8 * symbols[i] + symbols[j]] += 1
        count += 1
    assert all(values == [count // 64] * 64 for values in marginals.values())
    linear_checks = check_coefficients(code, distances)
    print(f"{count} guard checks, {len(pairs)} marginals and {linear_checks} coefficient thresholds passed")


if __name__ == "__main__":
    main()
