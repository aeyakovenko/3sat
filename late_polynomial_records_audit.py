"""Finite checks for degree-three polynomials over GF(16) and movable SAT pins."""

from itertools import combinations, product
from math import comb


FIELD_SIZE = 16
MODULUS = 0b10011  # x^4 + x + 1
DEGREE_BOUND = 4
MASK = FIELD_SIZE - 1


def multiply(left, right):
    result = 0
    while right:
        if right & 1:
            result ^= left
        right >>= 1
        left <<= 1
        if left & FIELD_SIZE:
            left ^= MODULUS
    return result


def verdict(database, point):
    value = 0
    for index in reversed(range(DEGREE_BOUND)):
        coefficient = (database >> (4 * index)) & MASK
        value = multiply(value, point) ^ coefficient
    return value & 1


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            column = row.bit_length() - 1
            if column not in pivots:
                pivots[column] = row
                break
            row ^= pivots[column]
    return len(pivots)


def check_evaluation():
    assert all(any(multiply(a, b) == 1 for b in range(1, FIELD_SIZE))
               for a in range(1, FIELD_SIZE))
    rows = [
        sum(verdict(1 << bit, point) << bit for bit in range(16))
        for point in range(FIELD_SIZE)
    ]
    for points in combinations(range(FIELD_SIZE), DEGREE_BOUND):
        assert binary_rank([rows[z] for z in points]) == DEGREE_BOUND
    pair_sums = {rows[a] ^ rows[b] for a, b in combinations(range(FIELD_SIZE), 2)}
    assert len(pair_sums) == comb(FIELD_SIZE, 2)
    for subset in range(1 << FIELD_SIZE):
        selected = [row for i, row in enumerate(rows) if subset & (1 << i)]
        assert 1 << binary_rank(selected) >= comb(len(selected), 2)
    for database in range(1 << 16):
        for z, row in enumerate(rows):
            assert verdict(database, z) == ((database & row).bit_count() & 1)
    return comb(FIELD_SIZE, DEGREE_BOUND)


def positive_padded_unit(identifier):
    return f"{identifier} 1 2 0\n"


def record(first_name, second_name):
    result = positive_padded_unit(first_name) + positive_padded_unit(second_name)
    assert len(result) <= 32
    return result.ljust(32)


def names(raw_record):
    numbers = [int(token) for token in raw_record.split()]
    assert numbers[1:4] == numbers[5:8] == [1, 2, 0]
    return numbers[0], numbers[4]


def query_record(point, flag):
    return record(100 + (flag << 2) + (point >> 2), 200 + (point & 3))


def decode_query(raw_record):
    high, low = names(raw_record)
    return (((high - 100) & 3) << 2) + (low - 200), (high - 100) >> 2


def first_free(start, visited):
    address = start % 17
    while address in visited:
        address = (address + 1) % 17
    return address


def scan_with_held_out_word(database):
    # Replies influence the next address. The physical prefix can depend on X.
    assigned = {}
    next_address = 0
    for logical_bit in range(16):
        address = first_free(next_address, assigned)
        bit = (database >> logical_bit) & 1
        assigned[address] = record(300 + 2 * logical_bit + bit, 3)
        next_address = address + 4 + 3 * bit
    return assigned, first_free(next_address, assigned)


def evaluate_records(records):
    database = 0
    query = None
    seen_bits = set()
    for raw_record in records:
        first, second = names(raw_record)
        if second == 3:
            index, bit = divmod(first - 300, 2)
            assert index not in seen_bits
            seen_bits.add(index)
            database |= bit << index
        else:
            assert query is None
            query = decode_query(raw_record)
    assert seen_bits == set(range(16))
    point, flag = query
    return verdict(database, point) ^ flag


def check_slots():
    checked = 0
    for database in (0, 1, 0xFFFF, 0x1234, 0xBEEF):
        assigned, last = scan_with_held_out_word(database)
        assert len(assigned) == 16 and last not in assigned
        for point, flag in product(range(FIELD_SIZE), range(2)):
            physical = [assigned.get(i, query_record(point, flag)) for i in range(17)]
            assert evaluate_records(physical) == (verdict(database, point) ^ flag)
            checked += 1
    return checked


if __name__ == "__main__":
    print(f"Verified {check_evaluation()} full-rank query sets and 1,048,576 verdicts.")
    print(f"Verified {check_slots()} aligned record completions of adaptive prefixes.")
