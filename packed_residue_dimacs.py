"""Compile compact residue guards over binary decimal-name digits into proper DIMACS."""

from itertools import combinations, product


def parse_proper_dimacs(data):
    """Read a single DIMACS instance, including multi-line clauses and comments."""
    header = None
    clauses = []
    pending = []
    for line in data.splitlines():
        fields = line.split()
        if not fields or fields[0] == b"c":
            continue
        if fields[0] == b"p":
            if header is not None or len(fields) != 4 or fields[1] != b"cnf":
                raise ValueError("invalid DIMACS header")
            header = tuple(int(v) for v in fields[2:])
            if min(header) < 0:
                raise ValueError("negative DIMACS count")
            continue
        if header is None:
            raise ValueError("clause data precedes header")
        for token in fields:
            literal = int(token)
            if literal:
                if abs(literal) > header[0] or len(pending) == 3:
                    raise ValueError("invalid proper ternary clause")
                pending.append(literal)
            else:
                if len({abs(x) for x in pending}) != 3:
                    raise ValueError("expected three distinct variables")
                clauses.append(tuple(pending))
                pending.clear()
    if header is None or pending or len(clauses) != header[1]:
        raise ValueError("incorrect DIMACS clause count or unterminated clause")
    return tuple(clauses)


def render_proper(clauses, variable_count):
    chunks = [f"p cnf {variable_count} {len(clauses)}\n"]
    chunks.extend(f"{a} {b} {c} 0\n" for a, b, c in clauses)
    return "".join(chunks).encode("ascii")


def packed_guard(payload, records, *, width=None):
    """Return proper DIMACS bytes. Each integer record supplies width binary digits.

    payload is a proper DIMACS byte string. The production width is
    floor(log10(record count)), with a one-digit minimum. width is exposed
    so small test instances can exercise several physical digits.
    """
    return _packed_guard(payload, records, width, 3, 1, {1}, pass_index=1)


def packed_guard_all_fields(payload, records, *, width=None):
    """Gate an arbitrary proper payload by the CRT (3,5) total-weight predicate.

    At S=0 return the source verdict. Otherwise accept exactly when
    ((S mod 3) + (S mod 5)) mod 3 = 1, where S is the total Hamming weight.
    """
    passed = {s for s in range(15) if (s % 3 + s % 5) % 3 == 1}
    return _packed_guard(payload, records, width, 15, 10, passed, pass_index=None)


def _packed_guard(payload, records, width, modulus, first_tag, passed, pass_index):
    source = parse_proper_dimacs(payload)
    t = len(records)
    if t == 0:
        raise ValueError("expected at least one record")
    if width is None:
        width = max(1, len(str(t)) - 1)
    if width < 1 or any(not 0 <= record < (1 << width) for record in records):
        raise ValueError("record out of range")

    # (tag+first_tag)*scale + spell[u] has decimal digits TAG || binary(u),
    # leading zeros included. Popcounts and spellings are built without
    # assuming a unit-cost popcount instruction.
    scale = 10**width
    spell = [0] * (1 << width)
    residue = [0] * (1 << width)
    for value in range(1, 1 << width):
        parent, digit = divmod(value, 2)
        spell[value] = 10 * spell[parent] + digit
        residue[value] = (residue[parent] + digit) % modulus

    def name(value, tag):
        return (tag + first_tag) * scale + spell[value]

    # No assumption of density on the supplied payload variable names.
    ordinary = (first_tag + modulus) * scale
    # A decimal trie avoids allocating by the largest input ID or relying
    # on expected constant-time hashing. Every pass follows actual digits.
    links = [[-1] * 10]
    labels = [0]
    renamed = []
    for clause in source:
        converted = []
        for lit in clause:
            node = 0
            for digit in str(abs(lit)):
                d = ord(digit) - ord("0")
                child = links[node][d]
                if child == -1:
                    child = len(links)
                    links[node][d] = child
                    links.append([-1] * 10)
                    labels.append(0)
                node = child
            if not labels[node]:
                labels[node] = ordinary
                ordinary += 1
            converted.append(labels[node] if lit > 0 else -labels[node])
        renamed.append(tuple(converted))
    pad = tuple(range(ordinary, ordinary + 3))
    ordinary += 3
    out = []
    for assignment in range(1, 8):
        out.append(tuple(-v if assignment >> i & 1 else v for i, v in enumerate(pad)))

    def unit(lit):
        out.append((lit, pad[0], pad[1]))

    for value, r in enumerate(residue):
        for tag in range(modulus):
            u = name(value, tag)
            unit(u if tag == r else -u)

    current = tuple(range(ordinary, ordinary + modulus))
    ordinary += modulus
    for i, v in enumerate(current):
        unit(v if i == 0 else -v)
    for record in records:
        after = tuple(range(ordinary, ordinary + modulus))
        ordinary += modulus
        for i, old in enumerate(current):
            for j in range(modulus):
                out.append((-old, -name(record, j), after[(i + j) % modulus]))
        for i, j in combinations(range(modulus), 2):
            out.append((-after[i], -after[j], pad[0]))
        current = after
    for r in range(1, modulus):
        if r not in passed:
            unit(-current[r])
    allow_payload_bypass = -current[0] if pass_index is None else current[pass_index]
    for a, b, c in renamed:
        bridge = ordinary
        ordinary += 1
        out.extend(((a, b, bridge), (-bridge, c, allow_payload_bypass)))
    return render_proper(out, ordinary - 1)


def satisfiable(clauses):
    """Small independent DPLL oracle for auditing emitted bytes."""
    while clauses:
        if any(not clause for clause in clauses):
            return False
        unit = next((c[0] for c in clauses if len(c) == 1), None)
        if unit is None:
            v = abs(min(clauses, key=len)[0])
            return any(satisfiable(clauses + ((s,),)) for s in (v, -v))
        clauses = tuple(
            tuple(v for v in c if v != -unit) for c in clauses if unit not in c
        )
    return True


def audit():
    yes = b"c multiline source\np cnf 819 2\n-199 17\n818 0 199 -17 818 0\n"
    no = render_proper(
        [
            tuple(s * v for s, v in zip(row, (17, 199, 818)))
            for row in product((1, -1), repeat=3)
        ],
        819,
    )
    samples = bits = cases = 0
    for payload in (yes, no, b"p cnf 0 0\n"):
        payload_yes = satisfiable(parse_proper_dimacs(payload))
        for t, b in ((2, 1), (3, 1), (3, 2)):
            baseline = packed_guard(payload, [0] * t, width=b)
            supports = []
            for j in range(t * b):
                data = [0] * t
                data[j // b] = 1 << (j % b)
                single = packed_guard(payload, data, width=b)
                assert len(single) == len(baseline)
                change = [
                    i
                    for i, (old, new) in enumerate(zip(baseline, single))
                    if old != new
                ]
                assert len(change) == 9 and all(
                    (baseline[i], single[i]) == (48, 49) for i in change
                )
                supports.append(change)
            assert len(set().union(*supports)) == 9 * t * b
            bits += t * b
            for records in product(range(2**b), repeat=t):
                out = packed_guard(payload, records, width=b)
                predicted = bytearray(baseline)
                for j, positions in enumerate(supports):
                    if records[j // b] >> (j % b) & 1:
                        for i in positions:
                            predicted[i] ^= 1
                assert predicted == out
                r = sum(v.bit_count() for v in records) % 3
                assert satisfiable(parse_proper_dimacs(out)) == (
                    r == 1 or r == 0 and payload_yes
                )
                cases += 1
            samples += 1
    # At t=100 the default width must be two. Check the actual scale change
    # separately so the small exhaustions are independent of width selection.
    inputs = [(i * 3 + 1) % 4 for i in range(100)]
    assert packed_guard(yes, inputs) == packed_guard(yes, inputs, width=2)
    print(
        f"{cases} full byte renders and DPLL verdicts on {samples} source/shape pairs; "
        f"{bits} disjoint digit supports verified."
    )


def audit_all_fields(use_pycosat=False):
    if use_pycosat:
        import pycosat

        def solve(clauses):
            return pycosat.solve(clauses) != "UNSAT"
    else:
        solve = satisfiable

    no = render_proper(
        [
            tuple(v * s for v, s in zip((3, 9, 15), signs))
            for signs in product((1, -1), repeat=3)
        ],
        15,
    )
    yes = b"p cnf 3 1\n1 -2 3 0\n"
    t, width = 3, 2
    allowed = {2, 6, 9, 10, 13}
    cases = checks = 0
    for payload, payload_sat in ((yes, True), (no, False)):
        base = packed_guard_all_fields(payload, [0] * t, width=width)
        supports = []
        for j in range(t * width):
            recs = [0] * t
            recs[j // width] = 1 << (j % width)
            toggled = packed_guard_all_fields(payload, recs, width=width)
            support = [p for p, (a, b) in enumerate(zip(base, toggled)) if a != b]
            assert len(base) == len(toggled) and len(support) == 225
            assert all((base[p], toggled[p]) == (48, 49) for p in support)
            supports.append(support)
        assert len(set().union(*supports)) == 225 * t * width
        for controls in product(range(2**width), repeat=t):
            out = packed_guard_all_fields(payload, controls, width=width)
            prediction = bytearray(base)
            for j, support in enumerate(supports):
                if controls[j // width] >> (j % width) & 1:
                    for pos in support:
                        prediction[pos] ^= 1
            assert prediction == out
            cases += 1
            if use_pycosat or controls in ((0, 0, 0), (1, 0, 0), (3, 0, 0)):
                weight = sum(x.bit_count() for x in controls)
                assert solve(parse_proper_dimacs(out)) == (
                    weight in allowed or weight == 0 and payload_sat
                )
                checks += 1
        if use_pycosat:
            for weight in range(31):
                records = [3] * (weight // 2) + [1] * (weight % 2)
                records += [0] * (15 - len(records))
                out = packed_guard_all_fields(payload, records, width=2)
                r = weight % 15
                assert solve(parse_proper_dimacs(out)) == (
                    r in allowed or r == 0 and payload_sat
                )
                checks += 1
    print(
        f"Mod 15: {cases} affine byte predictions on two six-digit cubes, "
        f"225 copies per digit; {checks} independent SAT checks."
    )


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--pycosat",
        action="store_true",
        help="also use installed pycosat to test two full mod-15 periods",
    )
    args = parser.parse_args()
    audit()
    audit_all_fields(args.pycosat)
