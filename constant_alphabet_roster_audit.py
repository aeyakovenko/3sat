"""Finite checks for erased-column selection, adaptive placements and diagonal certificates.

The single-query check uses the [15,4,8] simplex code. A separate grouped
variant uses [7,3,4] with duplicated columns. No asymptotic coding theorem
is inferred.
"""

from collections import Counter
from itertools import combinations, product


def subsets(items, k):
    for size in range(k + 1):
        yield from combinations(items, size)


def linear_outputs(columns):
    """List the image for every input in binary-mask order."""
    image = [0]
    for column in columns:
        image.extend([current ^ column for current in image])
    return image


def after_erasures(columns, erased, output_bits):
    allowed = [(j, value) for j, value in enumerate(columns) if j not in erased]
    pivots = {}
    basis = []
    for j, value in allowed:
        reduced = value
        while reduced and reduced.bit_length() in pivots:
            reduced ^= pivots[reduced.bit_length()]
        if reduced:
            pivots[reduced.bit_length()] = reduced
            basis.append(j)
        if len(basis) == output_bits:
            break
    return tuple(basis)


def check_erasure_limit():
    columns = tuple(range(1, 8))
    distance = min(sum((row & col).bit_count() % 2 for col in columns) for row in columns)
    assert distance == 4
    tests = 0
    for erased in subsets(range(7), distance - 1):
        basis = after_erasures(columns, erased, 3)
        assert len(basis) == 3 and set(basis).isdisjoint(erased)
        free = [col for j, col in enumerate(columns) if j not in erased]
        free_image = linear_outputs(free)
        fixed_image = linear_outputs([columns[j] for j in erased])
        for fixed in fixed_image:
            counts = Counter(fixed ^ free_part for free_part in free_image)
            assert sorted(counts) == list(range(8))
            assert len(set(counts.values())) == 1
            tests += 1
    obstruction = tuple(j for j, column in enumerate(columns) if column & 1)
    assert len(obstruction) == distance
    assert len(after_erasures(columns, obstruction, 3)) == 2
    print(f'{tests} fixed-content erasures have every output equally often; failure at exact distance {distance}')


def common_layout(database, programs, quota, columns, width):
    """Each program reads a private adaptive address sequence on shared immutable packets."""
    assigned = {}
    information = []
    m = len(columns)
    for step, base in programs:
        seen = set()
        position = base
        while len(seen) < quota:
            while position in seen:
                position = (position + 1) % m
            if position not in assigned:
                ordinal = len(assigned)
                assigned[position] = database >> (ordinal % 4) & 1
            seen.add(position)
            read = assigned[position]
            position = (position + step + 3 * read) % m
        information.append(seen)
    visited = frozenset(assigned)
    tag = next(j for j in range(m) if j not in visited)
    basis = after_erasures(columns, visited | {tag}, width)
    assert len(basis) == width
    holes = set(basis) | {tag}
    assert all(seen.isdisjoint(holes) for seen in information)
    available = [p for p in range(m) if p not in assigned and p not in holes]
    for ordinal, p in enumerate(available, len(assigned)):
        assigned[p] = database >> (ordinal % 4) & 1
    assert len(assigned) + len(holes) == m
    return visited, tag, basis


def group_value(database, group):
    return database >> (2 * group) & 3


def check_roster_queries():
    columns = tuple(range(1, 8)) * 2
    layouts = set()
    tests = 0
    for programs in (((1, 0), (2, 1)), ((4, 9), (3, 2), (1, 8))):
        for database in range(16):
            visited, tag, basis = common_layout(database, programs, 2, columns, 3)
            assert len(visited) <= 2 * len(programs)
            committed = visited | {tag}
            assert len(committed) < 8  # the doubled code has distance eight
            layouts.add((tag, basis))
            outputs = linear_outputs([columns[position] for position in basis])
            assert sorted(outputs) == list(range(8))
            for group, value in product(range(2), range(4)):
                wanted = group | (value << 1)
                reply_mask = outputs.index(wanted)
                native_bits = [0] * len(columns)
                for j, position in enumerate(basis):
                    native_bits[position] = reply_mask >> j & 1
                reconstructed = 0
                for bit, column in zip(native_bits, columns, strict=True):
                    if bit:
                        reconstructed ^= column
                assert reconstructed == wanted and not native_bits[tag]
                equal = (reconstructed >> 1) == group_value(database, reconstructed & 1)
                answers = tuple(tag_value == equal for tag_value in (0, 1))
                assert answers in ((True, False), (False, True))
                assert answers[1] == (value == group_value(database, group))
                tests += 1
    assert len(layouts) > 1
    print(f'{tests} group queries on {len(layouts)} adaptive hole layouts have exact opposite verdicts')



def check_diagonal():
    columns = tuple(range(1, 16))
    signatures = 0
    tests = 0
    for roster in (((1, 0), (2, 1)), ((4, 9), (3, 2), (1, 8))):
        tables = []
        seen_signatures = {}
        for a in range(16):
            header, tag, basis = common_layout(a, roster, 2, columns, 4)
            assert len(header) + 1 < 8
            # Only the exposed positions enter the common header; tag and
            # response positions are publicly reconstructed, with no data bits.
            public_tag = next(p for p in range(15) if p not in header)
            public_basis = after_erasures(columns, header | {public_tag}, 4)
            assert (tag, basis) == (public_tag, public_basis)
            image = linear_outputs([columns[p] for p in public_basis])
            assert sorted(image) == list(range(16))
            for x in range(16):
                response = image.index(x)
                assert image[response] == x
                assert [tag_value == (image[response] == a) for tag_value in (0, 1)] == [x != a, x == a]
                tests += 1
            # Independent indices for three programs: these bit permutations
            # place their two-bit input pieces at different numerical addresses.
            low, high = a & 3, a >> 2
            tables.append((header, (low, high, 3 ^ high, 3 ^ low, low ^ high, high)))
        for a, (header, cells) in enumerate(tables):
            for choice in ((0, 1), (2, 3), (4, 5)):
                observations = tuple((i, cells[i]) for i in choice)
                # The target file x=a and the sign/program chosen to obtain
                # this transcript do not enter the dictionary signature.
                for b, (other_header, other) in enumerate(tables):
                    compatible = header == other_header and all(other[i] == w for i, w in observations)
                    assert not compatible or a == b
                assert seen_signatures.setdefault((header, observations), a) == a
                signatures += 1
    print(f'{tests} canonical single queries and {signatures} authentic header/word certificates checked')


def check_certificates():
    # Columns stand for distinct addresses in independent read-only encodings
    # of each database, possibly selected by different programs for each query.
    databases = range(16)
    representations = [(a & 3, a >> 2, 3 ^ (a & 3), 3 ^ (a >> 2),
                        (a & 3) ^ (a >> 2)) for a in databases]
    unions = 0
    chosen = {}
    for a, cells in enumerate(representations):
        certificates = []
        for group in range(2):
            value = group_value(a, group)
            admissible = []
            for addresses in subsets(range(len(cells)), 2):
                if all(any(cells[i] != other[i] for i in addresses) or group_value(b, group) == value
                       for b, other in enumerate(representations)):
                    admissible.append(addresses)
            assert admissible
            certificates.append(admissible)
        for first, second in product(*certificates):
            merged = tuple((i, cells[i]) for i in sorted(set(first + second)))
            assert all(b == a or any(other[i] != word for i, word in merged)
                       for b, other in enumerate(representations))
            assert chosen.setdefault(merged, a) == a
            unions += 1
    print(f'{unions} diagonal certificate unions identify their four-bit databases')


if __name__ == '__main__':
    check_erasure_limit()
    check_diagonal()
    check_roster_queries()
    check_certificates()
