"""Check the native CNF, its OR read window, and simultaneous integer/binary checks."""
from itertools import combinations, combinations_with_replacement, product

from boolean_history_catalog_audit import BinaryField, polynomial_product


def encode(switches):
    count = len(switches)
    # A clause forbidding each anchor assignment other than 001.
    rows = [
        tuple(-i if bit else i for i, bit in enumerate(bits, start=1))
        for bits in product(range(2), repeat=3) if bits != (0, 0, 1)
    ]
    previous = 2
    for j, bit in enumerate(switches):
        selector, state = 4 + j, 4 + count + j
        rows.extend([
            (-selector, 2 + bit, 1),
            (-previous, state, 1),
            (-selector, state, 1),
            (previous, selector, -state),
        ])
        previous = state
    rows.append((previous, 1, 2))
    body = "".join(f"{a} {b} {c} 0\n" for a, b, c in rows)
    return f"p cnf {3 + 2 * count} {len(rows)}\n".encode() + body.encode()


def parse(file):
    lines = file.splitlines()
    p, cnf, variables, clauses = lines[0].split()
    assert (p, cnf) == (b"p", b"cnf") and int(clauses) == len(lines) - 1
    rows = []
    for line in lines[1:]:
        a, b, c, zero = map(int, line.split())
        row = (a, b, c)
        names = {abs(i) for i in row}
        assert zero == 0 and len(names) == 3 and min(names) >= 1
        assert max(names) <= int(variables)
        rows.append(row)
    assert set(range(1, int(variables) + 1)) == {abs(i) for row in rows for i in row}
    return rows


def satisfiable(rows):
    if not rows:
        return True
    shortest = min(rows, key=len)
    if not shortest:
        return False
    choices = shortest if len(shortest) == 1 else (shortest[0], -shortest[0])
    for chosen in choices:
        residual = [tuple(i for i in row if i != -chosen) for row in rows if chosen not in row]
        if satisfiable(residual):
            return True
    return False


def packed_bits(bits):
    return sum(bit << j for j, bit in enumerate(bits))


def block_reads(switches, order):
    mask = tuple(k.bit_count() % 2 for k in range(1 << order))
    return [bit ^ sign for bit in switches for sign in mask]


def verdict(reads, order):
    return any(bit ^ ((k % (1 << order)).bit_count() % 2) for k, bit in enumerate(reads))


def binary_rank(columns):
    pivots = {}
    for value in columns:
        while value:
            leading = value.bit_length() - 1
            if leading not in pivots:
                pivots[leading] = value
                break
            value ^= pivots[leading]
    return len(pivots)


def check_optimal_probe_rank(field):
    cases = 0
    for d in range(4):
        for points in combinations_with_replacement(range(field.size), d):
            degree = sum(poly.bit_length() - 1 for poly in
                         {field.minimal_polynomial(point) for point in points})
            for length in range(1, 11):
                columns = [
                    sum(field.power(a, j) << (i * field.width) for i, a in enumerate(points))
                    for j in range(length)
                ]
                assert binary_rank(columns) == min(length, degree)
                for probes in range(min(2, length) + 1):
                    def rank_with_pins(positions):
                        # Omitting pinned columns measures the freedoms after they are fixed.
                        return len(positions) + binary_rank(
                            value for j, value in enumerate(columns) if j not in positions
                        )
                    optimum = min(length, degree + probes)
                    assert max(rank_with_pins(pins) for pins in combinations(range(length), probes)) == optimum
                    assert rank_with_pins(range(length - probes, length)) == optimum
                    cases += 1
    return cases


def main():
    files = flips = checks = 0
    for count in range(1, 8):
        blank = encode((0,) * count)
        offsets = set()
        for j in range(count):
            changed = encode(tuple(int(i == j) for i in range(count)))
            assert len(blank) == len(changed)
            xor = [a ^ b for a, b in zip(blank, changed)]
            assert sum(v.bit_count() for v in xor) == 1
            offsets.add(xor.index(1))
            flips += 1
        assert len(offsets) == count
        for switches in product(range(2), repeat=count):
            assert satisfiable(parse(encode(switches))) == bool(max(switches))
            files += 1
    field = BinaryField(3, 0b1011)
    ranks = check_optimal_probe_rank(field)
    for a, b in product(range(8), repeat=2):
        # Obtain a fixed binary polynomial with roots a and b independently of the block trick.
        outer = polynomial_product(field.minimal_polynomial(a), field.minimal_polynomial(b))
        candidate = [(outer >> j) & 1 for j in range(7)]
        assert any(candidate) and len(candidate) == 7
        for order in range(1, 6):
            honest = block_reads([0] * len(candidate), order)
            false = block_reads(candidate, order)
            assert not verdict(honest, order) and verdict(false, order)
            delta = [y - x for x, y in zip(honest, false)]
            assert all(sum(diff * k**u for k, diff in enumerate(delta)) == 0 for u in range(order))
            discrepancy = packed_bits([int(diff != 0) for diff in delta])
            assert all(field.evaluate(discrepancy, v) == 0 for v in (a, b))
            assert sum(diff != 0 for diff in delta) == sum(candidate) * (1 << order)
            checks += 1
    print(f"{files} native formulas; {flips} distinct single-bit flips across 7 base files; "
          f"{checks} joint binary evaluation and exact integer moment checks; {ranks} optimal probe ranks")


if __name__ == "__main__":
    main()
