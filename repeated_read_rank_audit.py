"""Enumerate columns for repeated table reads and compare their field ranks."""

from itertools import product
from math import comb, prod


def exact_columns(widths, query_count):
    tables = list(product(*(range(1 << width) for width in widths)))
    all_tables = (1 << len(tables)) - 1
    single_reads = []
    for address, width in enumerate(widths):
        for reply in range(1 << width):
            single_reads.append(
                sum(1 << index for index, table in enumerate(tables)
                    if table[address] == reply)
            )
    columns = {all_tables}
    for _ in range(query_count):
        columns = {old & read for old in columns for read in single_reads}
    return len(tables), columns


def field_rank(row_count, columns, prime):
    pivots = {}
    for column in columns:
        vector = [(column >> row) & 1 for row in range(row_count)]
        for row in range(row_count):
            leading = vector[row]
            if not leading:
                continue
            if row not in pivots:
                inverse = pow(leading, -1, prime)
                pivots[row] = [(entry * inverse) % prime for entry in vector]
                break
            vector = [(a - leading * b) % prime for a, b in zip(vector, pivots[row])]
    return len(pivots)


def predicted_rank(widths, query_count):
    return sum(prod((1 << width) - 1 for width, used in zip(widths, support) if used)
               for support in product((0, 1), repeat=len(widths))
               if sum(support) <= query_count)


def check_channels(widths, addresses):
    words = [range(1 << width) for width in widths]
    requested = set(addresses)
    cases = 0
    for table in product(*words):
        # Conditional on this table, only its actual nonzero private values
        # can receive a nonzero left factor.
        supports = [
            {i for i, used in enumerate(mask) if used}
            for mask in product((False, True), repeat=len(words))
        ]
        supports = [s for s in supports if s <= requested and all(table[i] for i in s)]
        for replies in product(*(words[i] for i in addresses)):
            claimed = dict(zip(addresses, replies))
            consistent = all(claimed[i] == value for i, value in zip(addresses, replies))
            required = {i for i, value in claimed.items() if value}
            total = 0
            if consistent:
                for support in supports:
                    if required <= support and all(table[i] == claimed[i] for i in required):
                        total += (-1) ** len(support - required)
            assert total == all(table[i] == value for i, value in zip(addresses, replies))
            cases += 1
    return cases


def ceil_log2(number):
    return (number - 1).bit_length()


def main():
    field_tests = 0
    for rows in range(1, 5):
        for widths in product(range(3), repeat=rows):
            if sum(widths) > 5:
                continue
            for query_count in range(rows + 2):
                table_count, columns = exact_columns(widths, query_count)
                expected = predicted_rank(widths, query_count)
                for prime in (2, 3, 5):
                    assert field_rank(table_count, columns, prime) == expected
                    field_tests += 1

    protocol_tests = 0
    for rows in range(2, 65):
        for width in range(ceil_log2(rows), ceil_log2(rows) + 4):
            rank = 0
            for queries in range(rows + 1):
                rank += comb(rows, queries) * ((1 << width) - 1) ** queries
                cost = ceil_log2(comb(rows, queries)) + width * queries
                assert 0 <= cost - ceil_log2(rank) <= 2
                protocol_tests += 1

    channel_tests = sum(check_channels(widths, addresses)
                        for widths in ((0, 1), (1, 2), (1, 1, 1))
                        for length in range(4)
                        for addresses in product(range(len(widths)), repeat=length))

    print(f"Passed {channel_tests} signed channels, {field_tests} field ranks and {protocol_tests} protocol costs.")


if __name__ == "__main__":
    main()
