"""Degrees of the binary product graph, by coefficients in its two right banks."""

from itertools import combinations, combinations_with_replacement, product


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def binary_rank(vectors):
    basis = {}
    for value in vectors:
        while value:
            lead = value.bit_length() - 1
            if lead not in basis:
                basis[lead] = value
                break
            value ^= basis[lead]
    return len(basis)


def multiply(a, b, side):
    rows = [(a >> (i * side)) & ((1 << side) - 1) for i in range(side)]
    cols = [sum(((b >> (i * side + j)) & 1) << i for i in range(side))
            for j in range(side)]
    return sum(((row & col).bit_count() % 2) << (i * side + j)
               for i, row in enumerate(rows) for j, col in enumerate(cols))


def transform_masks(width):
    return [sum(1 << x for x in range(1 << width) if not x & (1 << j))
            for j in range(width)]


def mobius(table, masks):
    for j, low in enumerate(masks):
        table ^= (table & low) << (1 << j)
    return table


def direct_degree(side):
    width = side**2
    basis = [(a, b, multiply(a, b, side)) for a, b in
             product(range(1 << width), repeat=2)]
    table = sum(1 << (a | (b << width) | (c << (2 * width))) for a, b, c in basis)
    coeff = mobius(table, transform_masks(3 * width))
    top = sum((-1)**(3*width-a.bit_count()-b.bit_count()-c.bit_count())
              for a, b, c in basis)
    assert top == 1 << (2 * width - side)
    return max(j.bit_count() for j in bits(coeff))


def coefficient_degree(side):
    width = side**2
    count = 1 << width
    all_columns = (1 << side) - 1
    by_support = []
    for columns, free_c in product(range(1 << side), repeat=2):
        order = columns.bit_count() + free_c.bit_count()
        if order > side:
            continue
        indicator = 0
        for a in range(count):
            vectors = [sum(((a >> (i*side+k)) & 1) << i
                           for i in bits(all_columns ^ free_c)) for k in bits(columns)]
            if binary_rank(vectors) == columns.bit_count():
                indicator |= 1 << a
        by_support.append((order, indicator))
    masks = transform_masks(width)
    weights = [sum(1 << x for x in range(count) if x.bit_count() == j)
               for j in range(width+1)]
    highest = 0
    for selection in combinations_with_replacement(by_support, side):
        order = sum(w for w, _ in selection)
        if order + width <= highest:
            continue
        truth = (1 << count) - 1
        for _, indicator in selection:
            truth &= indicator
        coeff = mobius(truth, masks)
        if coeff:
            degree = max(j for j, weight in enumerate(weights) if coeff & weight)
            highest = max(highest, order + degree)
    return highest


def inverse(matrix, d):
    rows = [(matrix >> (d*i) & ((1 << d)-1)) | (1 << (d+i)) for i in range(d)]
    for i in range(d):
        pivot = next((j for j in range(i, d) if rows[j] >> i & 1), None)
        if pivot is None:
            return None
        rows[i], rows[pivot] = rows[pivot], rows[i]
        for j in range(d):
            if j != i and rows[j] >> i & 1:
                rows[j] ^= rows[i]
    return sum((row >> d) << (d*i) for i, row in enumerate(rows))


def gl4_exclusion():
    pairs = [(a, inv) for a in range(1 << 16) if (inv := inverse(a, 4)) is not None]
    assert len(pairs) == 20160
    assert all(multiply(a, inv, 4) == 0x8421 for a, inv in pairs)
    universe = (1 << len(pairs)) - 1

    def monomial_tables(bank):
        columns = [sum(1 << i for i, pair in enumerate(pairs) if pair[bank] >> j & 1)
                   for j in range(16)]
        for degree in range(4):
            for terms in combinations(columns, degree):
                table = universe
                for term in terms:
                    table &= term
                yield table

    left, right = list(monomial_tables(0)), list(monomial_tables(1))
    assert len(left) * len(right) == 485809
    assert all((x & y).bit_count() % 2 == 0 for x in left for y in right)
    print("d=4: 485809 vanishing mixed moments on GL_4 exclude degree 29; exact degree 28")


if __name__ == "__main__":
    for d, expected in ((1, 2), (2, 7), (3, 16)):
        degree = coefficient_degree(d)
        assert degree == expected
        if d <= 2:
            assert direct_degree(d) == degree
        else:
            width = d*d
            top = sum((-1)**(3*width-a.bit_count()-b.bit_count()-multiply(a,b,d).bit_count())
                      for a,b in product(range(1 << width), repeat=2))
            assert top == 1 << (2*width-d)
        assert d*d + (3*d*d+3)//4 <= degree <= 2*d*d - ((d*d//4)+1)//2
        print(f"d={d}: exact binary graph degree {degree},"
              f" integer coefficient of the full monomial {1 << (2*d*d-d)}")
    gl4_exclusion()
