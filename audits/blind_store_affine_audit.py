"""Exhaustive small-cube checks for value-sensitive affine RAM loads."""

from itertools import combinations, product


def points(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def translate(space, x):
    return sum(1 << (y ^ x) for y in points(space))


def linear_spaces(n):
    found = {1}
    pending = [1]
    while pending:
        space = pending.pop()
        for x in range(1 << n):
            if space & (1 << x):
                continue
            extension = space | translate(space, x)
            if extension not in found:
                found.add(extension)
                pending.append(extension)
    return sorted(found)


def linear_bits(n):
    return [
        sum(((x & coefficient).bit_count() % 2) << x for x in range(1 << n))
        for coefficient in range(1 << n)
    ]


def flat_tables(n):
    spaces = linear_spaces(n)
    forms = linear_bits(n)
    full = (1 << (1 << n)) - 1
    affine = forms + [full ^ form for form in forms]
    through = [[translate(s, x) for s in spaces] for x in range(1 << n)]
    restrictions = {
        space: {form & space for form in affine}
        for space in {s for row in through for s in row}
    }
    return through, restrictions


def check_zero_inputs(n, truth, through, restrictions):
    vertex_mask = (1 << n) - 1
    zeroes = [x for x in range(1 << n) if not truth >> x & 1]
    extra_at_zero = False
    for base in zeroes:
        extensions = [x for x in zeroes if x & base == base]
        alpha = max(x.bit_count() for x in extensions)
        extra = any(
            x.bit_count() == alpha and truth >> (vertex_mask ^ x) & 1
            for x in extensions
        )
        max_zero_size = max(s.bit_count() for s in through[base] if not s & truth)
        max_affine_size = max(
            s.bit_count() for s in through[base] if truth & s in restrictions[s]
        )
        assert max_zero_size == 1 << alpha
        assert max_affine_size == 1 << (alpha + extra)
        if base == 0:
            extra_at_zero = extra
    return len(zeroes), extra_at_zero


def graph_loads():
    graph_count = extension_count = independent_inputs = 0
    for n in range(6):
        through, restrictions = flat_tables(n)
        edges = [1 << u | 1 << v for u, v in combinations(range(n), 2)]
        for chosen in range(1 << len(edges)):
            pairs = [edges[j] for j in points(chosen)]
            # Store 1 at the two-bit address (x_u,x_v), then read address 3.
            truth = 0
            for x in range(1 << n):
                memory = [0] * 4
                for edge in pairs:
                    u, v = points(edge)
                    address = 2 * ((x >> u) & 1) + ((x >> v) & 1)
                    memory[address] = 1
                truth |= memory[3] << x
            graph_count += 1
            num_zeroes, extra_at_zero = check_zero_inputs(n, truth, through, restrictions)
            extension_count += extra_at_zero
            independent_inputs += num_zeroes
    return graph_count, extension_count, independent_inputs


def monotone_functions():
    # Split on the highest input bit. Monotonicity requires low <= high.
    tables = [0, 1]
    functions = zero_inputs = 0
    for n in range(5):
        through, restrictions = flat_tables(n)
        for truth in tables:
            num_zeroes, _ = check_zero_inputs(n, truth, through, restrictions)
            zero_inputs += num_zeroes
            functions += 1
        if n < 4:
            tables = [
                low | (high << (1 << n))
                for low, high in product(tables, repeat=2)
                if not low & ~high
            ]
    return functions, zero_inputs


def dimension(flat):
    size = flat.bit_count()
    assert size and not size & (size - 1)
    return size.bit_length() - 1


def guard_partition_cost(flat, differences):
    """Uniform total codimension of the first failed equality partition."""
    residual = flat
    cost = 0
    for bit in differences:
        failing = residual & bit
        if failing:
            cost += failing.bit_count() * (dimension(flat) - dimension(failing))
        residual &= ~bit
        if not residual:
            break
    if residual:
        cost += residual.bit_count() * (dimension(flat) - dimension(residual))
    return residual, cost


def expected_branch_cost():
    checked = 0
    for n in range(1, 4):
        full = (1 << (1 << n)) - 1
        forms = linear_bits(n)
        affine = forms + [full ^ form for form in forms]
        flats = {translate(s, x) for s in linear_spaces(n) for x in range(1 << n)}
        for differences in product(affine, repeat=n):
            guard = full
            for bit in differences:
                guard &= ~bit
            for flat in flats:
                equal, cost = guard_partition_cost(flat, differences)
                assert equal == flat & guard
                if equal:
                    # Multiply 2(1-2^-rank) by the number of points.
                    assert cost == 2 * (flat.bit_count() - equal.bit_count())
                    checked += 1
    return checked


def load_rule(flat, stores, avoid):
    """Return the residual flat and selected affine payload (zero initially)."""
    for guard, differences, payload in reversed(stores):
        equal = flat & guard
        if not equal:
            continue
        if not avoid or equal == flat:
            return equal, payload
        failed_bit = next(bit for bit in differences if bit & flat)
        new_flat = flat & failed_bit
        assert dimension(new_flat) + 1 == dimension(flat)
        flat = new_flat
    return flat, 0


def two_store_loads():
    n = 2
    full = (1 << (1 << n)) - 1
    forms = linear_bits(n)
    payloads = forms + [full ^ form for form in forms]
    flats = {translate(s, x) for s in linear_spaces(n) for x in range(1 << n)}
    guards = {}
    for lo, hi in product(payloads, repeat=2):
        guards.setdefault(full & ~(lo | hi), (lo, hi))
    # Differences are between the blind store address and the load address.
    # With a zero load address we can realize every listed affine guard.
    records = [
        (guard, differences, payload)
        for guard, differences in guards.items()
        for payload in payloads
    ]
    checked = harmless = unsafe_equal_payload = 0
    for first, second in product(records, repeat=2):
        old = first[0] & first[2]
        actual = (second[0] & second[2]) | (~second[0] & old)
        for flat in flats:
            for avoid in (False, True):
                retained, payload = load_rule(flat, (first, second), avoid)
                assert retained and retained & flat == retained
                assert not (actual ^ payload) & retained
                checked += 1
            agree_on_hits = not (second[2] ^ old) & second[0] & flat
            assert agree_on_hits == (not (actual ^ old) & flat)
            harmless += int(agree_on_hits)
            if first[2] == second[2] and actual & flat:
                # Dropping both equal-valued stores would instead return zero.
                unsafe_equal_payload += 1
    assert unsafe_equal_payload
    return checked, harmless, unsafe_equal_payload


if __name__ == "__main__":
    graphs, extensions, independent_inputs = graph_loads()
    print(f"{graphs} graph store programs; {extensions} admit dimension alpha+1 at zero")
    print(f"{independent_inputs} independent inputs match both flat dimensions")
    functions, zeros = monotone_functions()
    print(f"{functions} monotone functions through dimension 4; {zeros} zero inputs checked")
    equality = expected_branch_cost()
    print(f"{equality} feasible equality/flat pairs match the expected cost")
    loads, harmless, unsafe = two_store_loads()
    print(f"{loads} store/flat load rules verified; {harmless} redundant last stores")
    print(f"{unsafe} equal-payload cases where dropping both stores changes the read")
