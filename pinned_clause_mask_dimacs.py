"""Affine bit projection of independent OR triples into ordinary ASCII DIMACS.

Run with Python 3: python pinned_clause_mask_dimacs.py
Source bit 3*i+j selects the '-' (1) or space (0) sign on name j+1 in
data row i. The seven pin rows force all three names false. Rows may repeat.
The second encoding uses one ASCII identifier bit per source bit.
"""

from itertools import product


def row(mask):
    if not 0 <= mask < 8:
        raise ValueError("a ternary sign mask must lie in [0,7]")
    literals = [(b"-" if mask & (1 << j) else b" ") + bytes([ord("1") + j])
                for j in range(3)]
    return b" ".join(literals) + b" 0\n"


def encode(masks):
    """An m-row source maps to 11*(m+7) + len(header) bytes."""
    header = f"p cnf 3 {7 + len(masks)}\n".encode("ascii")
    return header + b"".join(row(mask) for mask in (*range(1, 8), *masks))


def parse_and_solve(data, names=3):
    """Parse the emitted ASCII and return its satisfying assignments as integers."""
    lines = data.decode("ascii").splitlines()
    tag, kind, n_text, m_text = lines[0].split()
    assert (tag, kind) == ("p", "cnf")
    n, m = int(n_text), int(m_text)
    assert n == names and m == len(lines) - 1
    clauses = []
    for line in lines[1:]:
        tokens = tuple(map(int, line.split()))
        assert len(tokens) == 4 and tokens[-1] == 0
        clause = tokens[:-1]
        identifiers = tuple(abs(lit) for lit in clause)
        assert 1 <= identifiers[0] < identifiers[1] < identifiers[2] <= n
        clauses.append(clause)
    assert {abs(lit) for clause in clauses for lit in clause} == set(range(1, n + 1))

    def satisfies(x, clause):
        return any(((x >> (abs(lit) - 1)) & 1) == (lit > 0) for lit in clause)

    return tuple(x for x in range(1 << n) if all(satisfies(x, clause) for clause in clauses))


def affine_directions(m):
    """Disjoint byte positions, each copying its source bit in bit lanes 0,2,3."""
    header_bytes = len(f"p cnf 3 {m + 7}\n")
    return tuple(0x0d << (8 * (header_bytes + 11 * (7 + i) + 3 * j))
                 for i in range(m) for j in range(3))


def audit():
    yes = no = pivots = byte_edges = 0
    for m in range(5):
        directions = affine_directions(m)
        assert all(delta.bit_count() == 3 for delta in directions)
        assert sum(directions).bit_count() == 9 * m
        files, models = {}, {}
        for masks in product(range(8), repeat=m):
            source = sum(mask << (3 * i) for i, mask in enumerate(masks))
            data = encode(masks)
            assert len(data) == 11 * (m + 7) + len(f"p cnf 3 {m+7}\n")
            files[source] = int.from_bytes(data, "little")
            models[source] = parse_and_solve(data)
            assert models[source] == ((0,) if all(masks) else ())
            if models[source]:
                yes += 1
            else:
                no += 1

        for source, file_bits in files.items():
            for index, delta in enumerate(directions):
                # Check every undirected cube edge against its exact ASCII xor.
                if not (source >> index) & 1:
                    continue
                neighbor = source ^ (1 << index)
                assert file_bits ^ files[neighbor] == delta
                byte_edges += 1
                if models[source]:
                    last = ((source >> (3 * (index // 3))) & 7).bit_count() == 1
                    assert (not models[neighbor]) == last
                    pivots += last

    # Exercise variable-width decimal headers and arbitrarily many repeated rows.
    for m in (2, 3, 92, 93, 992, 993):
        masks = tuple(1 << (i % 3) for i in range(m))
        assert parse_and_solve(encode(masks)) == (0,)
        assert parse_and_solve(encode(masks[:-1] + (0,))) == ()
    assert pivots == sum(3 * m * 7 ** (m - 1) for m in range(1, 5))
    print(f"{yes + no} proper DIMACS files for 0..4 mask rows: {yes} uniquely SAT, {no} UNSAT")
    print(f"{byte_edges} cube edges have the predicted three-bit ASCII xor")
    print(f"{pivots} edges remove a last surviving literal and flip the SAT verdict")
    print("Passed six additional SAT/UNSAT pairs at decimal header boundaries")


def encode_identifiers(masks):
    """One adjustable low bit in each of the three data-row digit positions."""
    lines = [f"p cnf 7 {len(masks) + 21}\n"]
    for first in (1, 3, 5):
        # Leave the odd-even-odd assignment 101 on each overlapping triple.
        for forbidden in range(8):
            if forbidden == 5:
                continue
            lits = [-(first + j) if forbidden & (1 << j) else first + j for j in range(3)]
            lines.append(f"{lits[0]} {lits[1]} {lits[2]} 0\n")
    for mask in masks:
        if not 0 <= mask < 8:
            raise ValueError("a ternary data mask must lie in [0,7]")
        a, b, c = [2 * (j + 1) + ((mask >> j) & 1) for j in range(3)]
        lines.append(f"{a} {b} {c} 0\n")
    return "".join(lines).encode("ascii")


def audit_identifiers():
    yes = no = edges = pivots = 0
    for m in range(5):
        # Each group has seven 8-byte unsigned rows and ten minus signs.
        first_data = len(f"p cnf 7 {m+21}\n") + 3 * (7 * 8 + 10)
        directions = [1 << (8 * (first_data + 8 * i + 2 * j)) for i in range(m) for j in range(3)]
        files, models = {}, {}
        for masks in product(range(8), repeat=m):
            source = sum(mask << (3 * i) for i, mask in enumerate(masks))
            data = encode_identifiers(masks)
            assert len(data) == first_data + 8 * m
            models[source] = parse_and_solve(data, names=7)
            assert models[source] == ((0b1010101,) if all(masks) else ())
            files[source] = int.from_bytes(data, "little")
            if models[source]:
                yes += 1
            else:
                no += 1
        for source, file_bits in files.items():
            for i, direction in enumerate(directions):
                if not (source >> i) & 1:
                    continue
                neighbor = source ^ (1 << i)
                assert file_bits ^ files[neighbor] == direction
                assert direction.bit_count() == 1
                edges += 1
                if models[source]:
                    last = ((source >> (3 * (i // 3))) & 7).bit_count() == 1
                    assert (not models[neighbor]) == last
                    pivots += last
    print(f"Bit-once identifier projection: {yes} uniquely SAT, {no} UNSAT; "
          f"{edges} physical Hamming-one edges, {pivots} pivotal")


if __name__ == "__main__":
    audit()
    audit_identifiers()
