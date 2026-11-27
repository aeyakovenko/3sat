"""Exact tests for the degree of polynomial checks on translated tagged tables."""

from itertools import combinations_with_replacement, product


def translated_rows(prime, tag_fields):
    tags = list(product(range(prime), repeat=tag_fields))
    shifts = []
    for shift in tags:
        translated = [
            tuple((x + z) % prime for x, z in zip(tag, shift)) for tag in tags
        ]
        layouts = []
        for data in product(range(2), repeat=len(tags)):
            fields = []
            for tag in translated:
                fields.extend(tag)
                fields.append(data[tags.index(tag)])
            layouts.append(fields)
        shifts.append(layouts)
    return shifts


def monomial_values(prime, fields, degree, values, position=0):
    """Enumerate evaluations, with exponents reduced on the actual domains."""
    if position == len(fields):
        yield values
        return
    samples, max_exponent = fields[position]
    for exponent in range(min(degree, max_exponent) + 1):
        yield from monomial_values(
            prime, fields, degree - exponent, values, position + 1
        )
        values = [v * x % prime for v, x in zip(values, samples)]


def reduce_column(column, basis, prime, *, insert):
    for position, value in enumerate(column):
        if not value:
            continue
        if position not in basis:
            if insert:
                scale = pow(value, -1, prime)
                basis[position] = [v * scale % prime for v in column]
            return False
        pivot_row = basis[position]
        for index in range(position, len(column)):
            column[index] = (column[index] - value * pivot_row[index]) % prime
    return True


def can_separate_translations(prime, tag_fields, degree):
    shifts = translated_rows(prime, tag_fields)
    assignments = len(shifts[0])
    flat = [row for shift in shifts for row in shift]
    fields = []
    for j, column in enumerate(zip(*flat)):
        is_data = j % (tag_fields + 1) == tag_fields
        fields.append((column, 1 if is_data else prime - 1))
    basis = {}
    equations = (len(shifts) - 1) * assignments
    target = [0] * equations + [1]
    for values in monomial_values(prime, fields, degree, [1] * len(flat)):
        constraints = [
            (values[i] - values[i % assignments]) % prime
            for i in range(assignments, len(values))
        ]
        constraints.append((values[assignments - 1] - values[0]) % prime)
        reduce_column(constraints, basis, prime, insert=True)
    return reduce_column(target, basis, prime, insert=False)


def verify_separating_family(prime, tag_fields, data_fields):
    tags = list(product(range(prime), repeat=tag_fields))
    alphabet = list(product(range(prime), repeat=data_fields))
    rows = list(product(tags, alphabet))

    def signature(table):
        entries = []
        for tag in tags:
            values = [data for key, data in table if key == tag]
            entries.append(len(values) % prime)
            for j in range(data_fields):
                entries.append(sum(data[j] for data in values) % prime)
        return tuple(entries)

    valid = {}
    for data_by_tag in product(alphabet, repeat=len(tags)):
        source = tuple(zip(tags, data_by_tag))
        key = signature(source)
        assert key not in valid
        valid[key] = source
    total = matches = 0
    for candidate in combinations_with_replacement(rows, len(tags)):
        total += 1
        key = signature(candidate)
        if key in valid:
            matches += 1
            assert candidate == valid[key]
    assert matches == len(valid)
    return total, matches


if __name__ == "__main__":
    for prime, fields in [(2, 0), (2, 1), (2, 2), (3, 1), (5, 1)]:
        threshold = (prime - 1) * fields + 1
        assert not can_separate_translations(prime, fields, threshold - 1)
        assert can_separate_translations(prime, fields, threshold)
        print(f"F_{prime}, {fields} tag fields: first degree {threshold}")
    for prime, tag_fields, data_fields in [(2, 1, 2), (2, 2, 1), (3, 1, 1)]:
        count, valid = verify_separating_family(prime, tag_fields, data_fields)
        print(
            f"F_{prime}, {tag_fields} tag and {data_fields} data fields: "
            f"{valid} valid among {count} candidate multisets"
        )
