"""Finite checks for compact native computations with a free presentation."""

from argparse import ArgumentParser
from itertools import combinations, permutations, product
from subprocess import run


def guarded_dimacs(checks):
    """The first seven clauses retain only 000. Every other clause tests one Boolean."""
    rows = [tuple(-name if bit else name for name, bit in zip((1, 2, 3), pattern, strict=True))
            for pattern in product((0, 1), repeat=3) if any(pattern)]
    rows.extend((-1 if ok else 1, 2, 3) for ok in checks)
    return (f'p cnf 3 {len(rows)}\n' + ''.join(f'{a:2d} {b:2d} {c:2d} 0\n' for a, b, c in rows)).encode()


def models(raw):
    lines = raw.splitlines()
    tag, kind, variables, count = lines[0].split()
    assert (tag, kind, variables) == (b'p', b'cnf', b'3') and int(count) == len(lines) - 1
    rows = []
    for line in lines[1:]:
        a, b, c, z = map(int, line.split())
        assert z == 0 and {abs(a), abs(b), abs(c)} == {1, 2, 3}
        rows.append((a, b, c))
    return [bits for bits in product((0, 1), repeat=3)
            if all(any(bits[abs(lit) - 1] == (lit > 0) for lit in row) for row in rows)]


def trace_checks(chronological, sorted_events, order, inverse, claimed):
    checks = [claimed == 1]
    for i in range(len(chronological)):
        checks.extend((inverse[order[i]] == i, order[inverse[i]] == i,
                       sorted_events[i] == chronological[order[i]]))
        address, time, incoming, outgoing = sorted_events[i]
        previous = sorted_events[i - 1] if i else None
        checks.append(previous is None or previous[:2] < (address, time))
        checks.append(incoming == (previous[3] if previous and previous[0] == address else 0))
        checks.append(time != 2 or outgoing == incoming)
    return checks


def audit_memory(solver):
    trials = accepted = damaged = 0
    file_lengths = set()
    for first, second, index, claimed in product((0, 1), repeat=4):
        # Two writes followed by one indirect load; the witness chooses its address.
        chronological = [(0, 0, 0, first), (1, 1, 0, second), (index, 2, claimed, claimed)]
        for order, inverse in product(permutations(range(3)), repeat=2):
            sorted_events = [chronological[i] for i in order]
            checks = trace_checks(chronological, sorted_events, order, inverse, claimed)
            raw = guarded_dimacs(checks)
            positive = bool(models(raw))
            expected = (claimed == 1 and (first, second)[index] == 1
                        and sorted_events == sorted(chronological)
                        and all(inverse[order[i]] == i for i in range(3)))
            assert positive == expected
            file_lengths.add(len(raw))
            accepted += positive
            trials += 1
            if solver:
                result = run([solver, '-q'], input=raw, capture_output=True, check=False)
                assert result.returncode == (10 if expected else 20)
            if positive:
                for i in range(3):
                    row = sorted_events[i]
                    broken = sorted_events.copy()
                    broken[i] = (*row[:3], 1 - row[3])
                    assert not models(guarded_dimacs(trace_checks(chronological, broken, order, inverse, claimed)))
                    damaged += 1
    assert len(file_lengths) == 1 and accepted == 4
    print(f'{trials} three-variable physical formulas of one length; {accepted} accepting, {damaged} damaged rows rejected')


def width_closure(n, accepted, width):
    masks = [sum(1 << i for i in ix) for ix in combinations(range(n), width)]
    views = [(mask, {x & mask for x in accepted}) for mask in masks]
    return {x for x in range(1 << n) if all((x & mask) in view for mask, view in views)}


def audit_parity():
    even4 = [x for x in range(16) if x.bit_count() % 2 == 0]
    best = 0
    for chosen in range(1 << len(even4)):
        accepted = {x for i, x in enumerate(even4) if chosen >> i & 1}
        if width_closure(4, accepted, 2) == accepted:
            best = max(best, len(accepted))
    assert best == 4
    cases = 0
    for width in (1, 2, 3, 6):
        blocks = 6 // width
        width_mask = (1 << width) - 1
        for witness_bits in range(blocks):
            pad_bits = blocks - 1 - witness_bits
            for x in range(64):
                block_parities = [((x >> (i * width)) & width_mask).bit_count() % 2 for i in range(blocks)]
                good_pads = 0
                for pad in range(1 << pad_bits):
                    extensions = 0
                    for witness in range(1 << witness_bits):
                        boundary_word = (pad << witness_bits) | witness
                        boundaries = [0, *(boundary_word >> i & 1 for i in range(blocks - 1)), 0]
                        extensions += all(b == (a ^ c) for b, a, c in
                                          zip(block_parities, boundaries[:-1], boundaries[1:], strict=True))
                    assert extensions <= 1
                    good_pads += extensions
                assert good_pads == int(x.bit_count() % 2 == 0)
                cases += 1
    print(f'Width-two CNF maximum on the four-bit even cube is {best}; {cases} exact witness/pad trades checked')


def field_product(a, b, degree, modulus):
    out = 0
    for _ in range(degree):
        if b & 1:
            out ^= a
        a <<= 1
        if a >> degree:
            a ^= modulus
        b >>= 1
    return out


def audit_polynomials():
    trials = 0
    for degree, modulus, k in ((2, 0b111, 1), (2, 0b111, 2), (2, 0b111, 3), (3, 0b1011, 4)):
        field_size = 1 << degree
        coordinates = 1 << k.bit_length()
        for coefficients in product(range(field_size), repeat=k):
            parity = 0
            for point in range(coordinates):
                value = 0
                for coefficient in reversed(coefficients):
                    value = field_product(value, point, degree, modulus) ^ coefficient
                parity ^= value & 1
            assert parity == 0
            trials += 1
    print(f'All {trials} finite-field polynomial seeds miss odd parity on the specified subcube')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--solver', help='optional CaDiCaL binary accepting DIMACS on stdin')
    audit_memory(parser.parse_args().solver)
    audit_parity()
    audit_polynomials()
