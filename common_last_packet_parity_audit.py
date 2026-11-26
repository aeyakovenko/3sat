"""Exhaustive checks for small common-master query packets with XOR recovery."""

from itertools import product
from operator import xor
from functools import reduce


def checked_unit(identifier):
    assert identifier not in (1, 2)
    return f"{identifier} 1 2 0\n"


def query_word(query, chunk_size, tag):
    # Separate high and low names, then the two complementary tagged outputs.
    clauses = []
    for bank, index in enumerate(query):
        high, low = divmod(index, chunk_size)
        clauses.append(checked_unit(100 + 10 * bank + high))
        clauses.append(checked_unit(200 + 10 * bank + low))
    clauses.append(checked_unit(72 + tag))
    text = "".join(clauses)
    assert len(text) <= 160
    return text.ljust(160).encode("ascii")


def count_completions(values, parities, erased):
    """Enumerate all genuinely free scalar bits after query selectors are pinned."""
    bank_count = len(values)
    chunks = len(values[0])
    num_regular = bank_count * chunks
    if erased == num_regular:
        return sum(
            all(reduce(xor, values[j], 0) == candidate[j] for j in range(bank_count))
            for candidate in product(range(2), repeat=bank_count)
        )
    bank, chunk = divmod(erased, chunks)
    assert all(reduce(xor, row, 0) == parities[j]
               for j, row in enumerate(values) if j != bank)
    others = values[bank][:chunk] + values[bank][chunk + 1:]
    possible_values = [
        candidate for candidate in range(2)
        if reduce(xor, others, candidate) == parities[bank]
    ]
    assert possible_values == [values[bank][chunk]]
    return len(possible_values)


def exhaust(bank_count, size, chunk_size):
    assert size % chunk_size == 0
    chunks = size // chunk_size
    raw_mask = (1 << chunk_size) - 1
    queries = list(product(range(size), repeat=bank_count))
    for query in queries:
        tag0 = query_word(query, chunk_size, 0)
        tag1 = query_word(query, chunk_size, 1)
        assert sum((a ^ b).bit_count() for a, b in zip(tag0, tag1)) == 1

    erasures = 0
    for tables in product(range(1 << size), repeat=bank_count):
        masks = [
            [(table >> (a * chunk_size)) & raw_mask for a in range(chunks)]
            for table in tables
        ]
        check_masks = [reduce(xor, row, 0) for row in masks]
        master_models = 0
        for query in queries:
            high_low = [divmod(index, chunk_size) for index in query]
            values = [
                [(mask >> low) & 1 for mask in row]
                for row, (_, low) in zip(masks, high_low)
            ]
            checks = [(mask >> low) & 1 for mask, (_, low) in zip(check_masks, high_low)]
            assert all(reduce(xor, row, 0) == check for row, check in zip(values, checks))
            selected = all(row[high] for row, (high, _) in zip(values, high_low))
            expected = all((table >> index) & 1 for table, index in zip(tables, query))
            assert selected == expected
            master_models += 1
            for slot in range(bank_count * chunks + 1):
                count = count_completions(values, checks, slot)
                tagged = [count * int(selected == tag) for tag in range(2)]
                assert tagged == [int(expected == tag) for tag in range(2)]
                erasures += 1
        assert master_models == size ** bank_count
    print(f"{bank_count} banks, {size} bits/bank, chunks of {chunk_size}: "
          f"{erasures:,} opposite-tag erasure pairs")
    return erasures


if __name__ == "__main__":
    cases = [(2, 4, 2), (4, 2, 1), (4, 2, 2)]
    total = sum(exhaust(*case) for case in cases)
    print(f"Verified {total:,} erasure pairs, with a unique positive in each pair.")
