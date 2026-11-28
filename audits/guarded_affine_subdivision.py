#!/usr/bin/env python3
"""Check the guarded paired-rail reduction on actual clauses and inserted-bit rows."""

from itertools import combinations, combinations_with_replacement, product


def dimacs(bound, clauses):
    header = f"p cnf {bound} {len(clauses)}\n"
    return header + "".join(" ".join(map(str, clause)) + " 0\n" for clause in clauses)


def parse(text):
    header, *lines = text.splitlines()
    kind, syntax, bound, count = header.split()
    assert (kind, syntax) == ("p", "cnf") and len(lines) == int(count)
    clauses = []
    for line in lines:
        *clause, zero = map(int, line.split())
        assert zero == 0 and all(0 < abs(lit) <= int(bound) for lit in clause)
        clauses.append(tuple(clause))
    return int(bound), clauses


def paired_rail(source):
    bound, clauses = parse(source)
    out = []
    for clause in clauses:
        assert len(clause) == len({abs(lit) for lit in clause}) == 3
        false_bits = []
        for lit in clause:
            p = int(f"{abs(lit)}0")
            q = int(f"{abs(lit)}1")
            out.extend([(-1, p, q), (-1, -p, -q)])
            false_bits.append(p if lit > 0 else q)
        out.append(tuple(-v for v in false_bits))
    return dimacs(10 * bound + 9, out)


def signed_rows(clauses, names):
    """One pair (positive mask, negative mask) per clause after dense renaming."""
    positions = {name: 1 << i for i, name in enumerate(names)}
    return [(sum(positions[v] for v in set(c) if v > 0),
             sum(positions[-v] for v in set(c) if v < 0)) for c in clauses]


def holds(rows, mask):
    return all((p & mask) or (n & ~mask) for p, n in rows)


def extend_basis(basis, mask):
    while mask:
        j = mask.bit_length() - 1
        if j not in basis:
            basis[j] = mask
            return
        mask ^= basis[j]


def check_source(clauses):
    original = sorted({abs(lit) for c in clauses for lit in c})
    source = dimacs(max(original, default=0), clauses)
    source_rows = signed_rows(clauses, original)
    models = sum(holds(source_rows, m) for m in range(1 << len(original)))

    guarded = paired_rail(source)
    _, context = parse(guarded)
    assert len(context) == 7 * len(clauses)
    assert all(len(c) == len({abs(lit) for lit in c}) == 3 for c in context)
    assert len(guarded) <= 24 * len(source)
    names = [1] + sorted({abs(lit) for c in context for lit in c} - {1})
    assert not {2, 3, 4}.intersection(names)
    h_rows = signed_rows(context, names)
    # The input assignment has bits for b, rails in sorted-name order, then x,y.
    k = len(names)
    ncoef = k + 3  # intercept, b/rail variables, x, y
    basis = {}
    on_models = 0
    misses_radius_three = False
    b_is_valid_correction = True
    for assignment in range(1 << k):
        h = holds(h_rows, assignment)
        b = assignment & 1
        weight = (assignment >> 1).bit_count()
        if not b and weight <= 2:
            assert h
        if not b and weight <= 3 and not h:
            misses_radius_three = True
        if b and h:
            on_models += 1
        for x, y in product(range(2), repeat=2):
            old = bool(h and (x or y))
            allowed = [t for t in range(2)
                       if bool(h and (x or t) and (t or y)) == old]
            xor = x ^ y
            assert xor in allowed
            if (xor ^ b) not in allowed:
                b_is_valid_correction = False
            if len(allowed) == 1:
                # A homogeneous linear condition on the affine correction to XOR.
                mask = assignment | (x << k) | (y << (k + 1))
                extend_basis(basis, 1 | (mask << 1))
    assert on_models == models
    assert misses_radius_three == bool(clauses)
    rule_count = 1 << (ncoef - len(basis))
    assert rule_count == (1 if models else 2)
    assert b_is_valid_correction == (models == 0)
    return rule_count


def check_wrapper(clauses):
    variables = sorted({abs(lit) for c in clauses for lit in c})
    source = dimacs(max(variables, default=0), clauses)
    source_rows = signed_rows(clauses, variables)
    source_model_count = sum(holds(source_rows, m) for m in range(1 << len(variables)))
    bound, context = parse(paired_rail(source))
    anchors = (5, 6, 7)
    pins = [tuple(-v if bad >> i & 1 else v for i, v in enumerate(anchors))
            for bad in range(1, 8)]
    common = pins + [(3, 1, 5), (-3, -1, 5)] + context
    files = [dimacs(bound, common + [(v, 5, 6)]).encode("ascii") for v in (3, 1)]
    easy, edited = files
    assert len(easy) == len(edited) and easy.splitlines()[0] == edited.splitlines()[0]
    assert sum((a ^ b).bit_count() for a, b in zip(easy, edited)) == 1
    assert easy.endswith(b"3 5 6 0\n") and edited.endswith(b"1 5 6 0\n")

    for hard, contents in enumerate(files):
        _, decoded = parse(contents.decode("ascii"))
        assert all(len(c) == len({abs(lit) for lit in c}) == 3 for c in decoded)
        controls = (1, 3, *anchors)
        rail_names = sorted({abs(lit) for c in decoded for lit in c} - set(controls))
        rows = signed_rows(decoded, [*controls, *rail_names])
        models = 0
        for data in range(1 << len(rail_names)):
            for ctrl in range(1 << len(controls)):
                answer = holds(rows, ctrl | (data << len(controls)))
                if answer:
                    models += 1
                    # Low bits encode b then a. The three anchor bits are zero.
                    assert ctrl == (1 if hard else 2)
                if not hard and ctrl == 2 and data.bit_count() <= 2:
                    assert answer
        if hard:
            assert models == source_model_count
        else:
            assert models >= 1
    return source_model_count != 0


def radius_three_check():
    # All multisets of up to three literals, allowing b, signs, tautologies,
    # repetitions and the empty clause. Ignore the input header bound.
    variables = (1, 2, 3, 4, 5)
    literals = tuple(v for i in variables for v in (i, -i))
    checked = 0
    for width in range(4):
        for clause in combinations_with_replacement(literals, width):
            rows = signed_rows([clause], variables)
            promised = all(holds(rows, z << 1) for z in range(16)
                           if z.bit_count() <= 3)
            tautology = any(-lit in clause for lit in clause)
            assert promised == (tautology or -1 in clause)
            if promised and not tautology:
                restricted = tuple(lit for lit in clause if lit != -1)
                assert len(restricted) <= 2
                smaller = signed_rows([restricted], variables[1:])
                for z in range(16):
                    assert holds(rows, (z << 1) | 1) == holds(smaller, z)
            checked += 1
    return checked


def main():
    names = (9, 10, 101)
    signed_triples = [tuple(s * v for s, v in zip(signs, names))
                      for signs in product((1, -1), repeat=3)]
    counts = {1: 0, 2: 0}
    for subset in range(256):
        clauses = [c for i, c in enumerate(signed_triples) if subset >> i & 1]
        counts[check_source(clauses)] += 1
    assert counts == {1: 255, 2: 1}

    # Widely separated decimal IDs and repeated source clauses stress the
    # physical name map and emission of a consistency pair per occurrence.
    four = (*names, 100000000000000000037)
    every = [tuple(sign * v for sign, v in zip(signs, support))
             for support in combinations(four, 3) for signs in product((1, -1), repeat=3)]
    cases = [every, every[::3], every[1::4], every[::7] * 2,
             signed_triples + [every[-1]], [every[0], every[-1]]]
    outcomes = [check_source(c) for c in cases]
    assert set(outcomes) == {1, 2}
    wrappers = [[], [signed_triples[0]], signed_triples[:-1], signed_triples, *cases]
    wrapped = [check_wrapper(c) for c in wrappers]
    assert set(wrapped) == {False, True}
    print(f"one-bit ordinary wrappers: {sum(wrapped)} SAT, {wrapped.count(False)} UNSAT on edited files")
    print(f"three-variable subsets: {counts[1]} unique, {counts[2]} with two rules")
    print(f"four-variable cases: {outcomes.count(1)} unique, {outcomes.count(2)} with two rules")
    print(f"radius-three clauses checked: {radius_three_check()}")


if __name__ == "__main__":
    main()
