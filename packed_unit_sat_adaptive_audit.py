"""Exact depth 1/2 census for a four-bit RAM deciding the packed SAT catalog."""

from itertools import product
from operator import and_, eq, lt, mul, or_, sub, xor

WORD_MASK = 15
ALL_INPUTS = (1 << 16) - 1
PACKED = tuple(range(16))
LITERALS = [tuple([c] * 16) for c in PACKED]
SOURCES = [*LITERALS, PACKED]


def signed(word):
    return word if word < 8 else word - 16


def satisfiable(bits):
    return any((a or b) and (not bits & 1 or a) and (not bits & 2 or not a)
               and (not bits & 4 or b) and (not bits & 8 or not b)
               for a, b in product((False, True), repeat=2))


def mask(table):
    return sum(1 << i for i, value in enumerate(table) if value)


TARGET = mask(map(satisfiable, PACKED))


def transformed(left, right, operation):
    return tuple(operation(a, b) & WORD_MASK for a, b in zip(left, right))


def branch_masks(left, right, comparisons):
    for comparator in comparisons:
        outcome = mask(map(comparator, left, right))
        yield outcome
        yield outcome ^ ALL_INPUTS


def adaptive_census(enable_signed):
    comparisons = [eq, lt]
    if enable_signed:
        comparisons.append(lambda a, b: signed(a) < signed(b))
    # Saturating-count and masked-count shifts can coexist in this stronger ISA.
    operations = [
        and_, or_, xor, lambda x, y: x + y, sub, mul,
        lambda x, y: x << y, lambda x, y: x >> y, lambda x, y: signed(x) >> y,
        lambda x, y: x << (y % 4), lambda x, y: x >> (y % 4),
        lambda x, y: signed(x) >> (y % 4),
        lambda x, y: (x << (y % 4)) | (x >> (4 - y % 4)),
        lambda x, y: (x >> (y % 4)) | (x << (4 - y % 4)),
    ]
    # Also allow comparisons materializing 0/1 registers in one instruction.
    operations.extend(comparisons)
    operations.extend(lambda x, y, compare=compare: not compare(x, y)
                      for compare in comparisons)

    initial_cuts = {cut for a, b in product(SOURCES, repeat=2)
                    for cut in branch_masks(a, b, comparisons)}
    assert TARGET not in initial_cuts
    tables = {transformed(a, b, op) for a, b in product(SOURCES, repeat=2)
              for op in operations} - set(SOURCES)

    # If the root is a data instruction, only a comparison using its result
    # offers a decision absent at depth one.
    successful_tables = sum(
        any(TARGET in branch_masks(a, b, comparisons)
            for source in SOURCES for a, b in [(table, source), (source, table)])
        for table in tables
    )

    # If the root is a branch, each restricted domain can use its own final
    # comparison. Constant verdicts belong to initial_cuts.
    def decidable_on(domain):
        return any((prediction ^ TARGET) & domain == 0 for prediction in initial_cuts)

    successful_cuts = {cut for cut in initial_cuts
                       if decidable_on(cut) and decidable_on(ALL_INPUTS ^ cut)}
    assert successful_tables == 0
    assert len(successful_cuts) == (2 if enable_signed else 0)
    family = "unsigned plus signed" if enable_signed else "unsigned"
    print(f"{family}: {len(initial_cuts)} branch masks, {len(tables)} data tables, "
          f"{successful_tables} successful data roots, {len(successful_cuts)} successful branch masks")


if __name__ == "__main__":
    adaptive_census(False)
    adaptive_census(True)
    for packed in PACKED:
        unsigned_decision = packed < 10 and (packed & 3) != 3
        signed_decision = packed != 3 if packed < 7 else signed(packed) < signed(10)
        assert unsigned_decision == signed_decision == satisfiable(packed)
    print("Both worst-case-optimal adaptive trees verified on all 16 inputs.")
