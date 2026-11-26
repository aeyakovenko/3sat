"""Check folded carry evaluation against direct binary linear recurrences.

Use Python 3, without dependencies. Symbolic pairs (u, v) denote exponents
u + 2**h * v. The period-two test forms its own rational generating function;
the independent reference simulation uses the original phase-specific delays.
"""

from functools import lru_cache
from itertools import product


def toggle(values, x):
    if x in values:
        values.remove(x)
    else:
        values.add(x)


def coefficients(terms, h):
    """Cancel equal *numerical* exponents, including different pair encodings."""
    representatives = {}
    for u, v in terms:
        exponent = u + (v << h)
        assert exponent >= 0
        if exponent in representatives:
            del representatives[exponent]
        else:
            representatives[exponent] = (u, v) if exponent else (0, 0)
    return representatives


def folded_inverse(terms, h, blocks):
    """Evaluate 1/Q via the product of Q(Y**(2**i)) for i < h*blocks.

    In characteristic two, multiplying this product by Q gives Q(Y**(2**(h*blocks))),
    which is 1 below the cutoff. Bit i=b*h+j contributes its u in row b
    and its v in row b+1, both in column j. Only the signed carries cross
    columns, with the final carry of each row fed into the next row's start.
    """
    support = coefficients(terms, h)
    assert 0 in support and h > 0 and blocks > 0
    choices = tuple(support.values())
    # Choose one term of the Frobenius factor for every bit in this column.
    # The final row has no factor of its own; it receives the last v offset.
    increments = set()
    for column in product(choices, repeat=blocks):
        shifted = tuple(column[b][0] + (column[b-1][1] if b else 0)
                        for b in range(blocks)) + (column[-1][1],)
        toggle(increments, shifted)

    @lru_cache(maxsize=None)
    def transitions(carry):
        by_output = {}
        for increment in increments:
            totals = tuple(x + y for x, y in zip(carry, increment))
            mask = sum((value % 2) << b for b, value in enumerate(totals))
            new_carry = tuple(value // 2 for value in totals)
            toggle(by_output.setdefault(mask, set()), new_carry)
        return by_output

    # Bound the carry into each next row using an ordinary low-to-high bit
    # scan. Dropping all target-bit conditions only enlarges these intervals.
    boundary_ranges = []
    minimum = maximum = 0
    for b in range(blocks):
        least = min(inc[b] for inc in increments)
        most = max(inc[b] for inc in increments)
        for _ in range(h):
            minimum = (minimum + least) // 2
            maximum = (maximum + most) // 2
        boundary_ranges.append(range(minimum, maximum + 1))

    @lru_cache(maxsize=None)
    def evaluate(target):
        assert 0 <= target < 1 << (h * blocks)
        masks = [sum(((target >> (b*h+j)) & 1) << b for b in range(blocks))
                 for j in range(h)]
        parity = 0
        for boundary in product(*boundary_ranges):
            live = {(0,) + boundary}
            for mask in masks:
                following = set()
                for carry in live:
                    following.symmetric_difference_update(transitions(carry).get(mask, ()))
                live = following
            # Carry out of each row must be the guessed carry into the next.
            # Both the high target row and its final carry must be zero.
            parity ^= int(boundary + (0,) in live)
        return parity

    return evaluate


def direct(due, sources, count):
    values = []
    for t in range(count):
        bit = int(t in sources)
        for lag in due[t % len(due)]:
            assert lag > 0
            if lag <= t:
                bit ^= values[t-lag]
        values.append(bit)
    return values


def check_scalar(h, blocks):
    stride = 1 << h
    # The last two pair encodings cancel at this width as numerical exponents.
    terms = [(0, 0), (1, 0), (-1, 1), (1, 1), (2, 1), (2+stride, 0)]
    inv = folded_inverse(terms, h, blocks)
    count = 1 << (h * blocks)
    cases = 0
    for sources in ({0}, {1, stride, stride+3}):
        expected = direct([[1, stride-1, stride+1]], sources, count)
        for t, bit in enumerate(expected):
            got = sum(inv(t-start) for start in sources if start <= t) % 2
            assert got == bit, ('scalar', h, blocks, t, bit, got)
            cases += 1
    return cases


def multiply(left, right):
    return [(u+x, v+y) for u, v in left for x, y in right]


def check_period_two(h, blocks):
    stride = 1 << h
    # In Z_a(Y) = sum_k z[2k+a]Y^k, build the two-by-two equation matrix.
    # Here the physical delay is u+2*stride*v before folding the phases.
    taps = (((1, 0), (-3, 1)), ((2, 0), (1, 1)))
    matrix = [[([(0, 0)] if a == b else []) for b in range(2)] for a in range(2)]
    for a, phase in enumerate(taps):
        for u, v in phase:
            b = (a-u) % 2
            matrix[a][b].append(((u+b-a)//2, v))
    (aa, ab), (ba, bb) = matrix
    determinant = multiply(aa, bb) + multiply(ab, ba)
    inv = folded_inverse(determinant, h, blocks)
    sources = {0, 3, 2*stride+1}
    impulses = [[(t//2, 0) for t in sources if t % 2 == b] for b in range(2)]
    numerators = [multiply(bb, impulses[0]) + multiply(ab, impulses[1]),
                  multiply(ba, impulses[0]) + multiply(aa, impulses[1])]
    offsets = [tuple(coefficients(poly, h)) for poly in numerators]
    count = 2 << (h * blocks)
    expected = direct([[1, 2*stride-3], [2, 2*stride+1]], sources, count)
    for t, bit in enumerate(expected):
        k, a = divmod(t, 2)
        got = sum(inv(k-start) for start in offsets[a] if start <= k) % 2
        assert got == bit, ('period two', h, blocks, t, bit, got)
    return count


def check_pin_and_phase_tests():
    """Independent finite tests of the partial-certificate and phase criteria."""
    pin_cases = 0
    for labels in product((None, 0, 1), repeat=5):
        completions = [bits for bits in product((0, 1), repeat=5)
                       if all(p is None or b == p for p, b in zip(labels, bits))]
        possible = {(sum(bits[:3]) % 2) & (sum(bits[3:]) % 2) for bits in completions}
        bank_values = []
        for bank in (labels[:3], labels[3:]):
            known_parity = sum(p == 1 for p in bank) % 2
            bank_values.append({j for j in (0, 1) if None in bank or known_parity == j})
        predicted = {a & b for a in bank_values[0] for b in bank_values[1]}
        assert predicted == possible
        pin_cases += 1

    phase_cases = 0
    for counts in product(range(5), repeat=4):
        errors = []
        for c, a, b in product((0, 1), repeat=3):
            errors.append(sum(count for (x, y), count in zip(product((0, 1), repeat=2), counts)
                              if (c ^ (a & x) ^ (b & y)) != (x & y)))
        assert min(errors) == min(counts)
        phase_cases += 1
    return pin_cases, phase_cases


def main():
    shapes = ((2, 2), (2, 3), (3, 2), (3, 3), (4, 2))
    scalar = sum(check_scalar(h, blocks) for h, blocks in shapes)
    phased = sum(check_period_two(h, blocks) for h, blocks in shapes)
    pin, phase = check_pin_and_phase_tests()
    print(f'{scalar} scalar and {phased} alternating-phase coefficients passed')
    print(f'{pin} partial-pin patterns and {phase} phase histograms passed')


if __name__ == '__main__':
    main()
