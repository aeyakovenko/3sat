"""Check affine prefix predecessors and a quadratic DIMACS scatter solver."""

from collections import Counter
from itertools import combinations, product
from random import Random


def consistent(equations):
    """Rows are (nonnegative coefficient mask, right-hand-side bit)."""
    basis = {}
    for mask, value in equations:
        while mask:
            pivot = mask.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (mask, value)
                break
            row, bit = basis[pivot]
            mask ^= row
            value ^= bit
        else:
            if value:
                return False
    return True


def max_affine(rows, prefix, d):
    eqs = [*rows, *prefix]
    if not consistent(eqs):
        return None
    result = 0
    for j in reversed(range(d)):
        trial = (1 << j, 1)
        if consistent([*eqs, trial]):
            eqs.append(trial)
            result |= 1 << j
        else:
            eqs.append((1 << j, 0))
    return result


def predecessor(rows, cutoff, d):
    if cutoff == 1 << d:
        return max_affine(rows, [], d)
    head = []
    best = None
    for j in reversed(range(d)):
        bit = (cutoff >> j) & 1
        if bit:
            candidate = max_affine(rows, [*head, (1 << j, 0)], d)
            if candidate is not None:
                best = candidate
        head.append((1 << j, bit))
    return best


def dimacs_file(clauses, variables):
    text = f"p cnf {variables} {len(clauses)}\n".encode()
    text += b"".join((" ".join(map(str, c)) + " 0\n").encode() for c in clauses)
    nbytes = max(len(text), ((1 << (variables + len(clauses))) + 7) // 8)
    return text.ljust(nbytes, b" ")


def parse_file(raw):
    header, *body = raw.splitlines()
    kind, fmt, names, length = header.split()
    assert (kind, fmt) == (b"p", b"cnf")
    vars_used = int(names)
    words = [int(t) for line in body for t in line.split()]
    assert len(words) == 4 * int(length)
    clauses = []
    for i in range(0, len(words), 4):
        literals = words[i:i + 3]
        assert words[i + 3] == 0 and len(set(map(abs, literals))) == 3
        assert all(1 <= abs(item) <= vars_used for item in literals)
        clauses.append(literals)
    return vars_used, clauses


def evaluate(clauses, x):
    return all(any(bool(x & (1 << (abs(y) - 1))) == (y > 0) for y in c) for c in clauses)


def direct_address(clauses, v, gray):
    u = gray >> v
    out = 0
    for j, clause in enumerate(clauses):
        a, b, c = [bool(gray & (1 << (abs(y) - 1))) != (y > 0) for y in clause]
        aux = bool(u & (1 << j))
        out |= (aux ^ (a and b)) << j
        out |= (aux and c) << (j + len(clauses))
    return out


def scatter(raw, counters):
    v, clauses = parse_file(raw)
    m = len(clauses)
    d = v + m
    steps = 1 << d
    assert steps <= len(raw) * 8
    masks = [{} for _ in range(4)]
    planes = [0, 0, 0, 0]
    for j, clause in enumerate(clauses):
        for role, literal in enumerate(clause):
            key = 1 << (abs(literal) - 1)
            masks[role][key] = masks[role].get(key, 0) | (1 << j)
            planes[role] |= (literal > 0) << j
        masks[3][1 << (v + j)] = 1 << j

    memory, matches = {}, 0
    schedule = []
    for i in range(steps):
        if i:
            flip = i & -i
            for plane, mask in enumerate(masks):
                planes[plane] ^= mask.get(flip, 0)
        a, b, c, u = planes
        address = (u ^ (a & b)) | ((u & c) << m)
        assert address == direct_address(clauses, v, i ^ (i >> 1))
        memory[address] = i + 1
        schedule.append(address)
        matches += address == 0

    solutions = sum(evaluate(clauses, x) for x in range(1 << v))
    assert matches == solutions
    assert (memory.get(0, 0) != 0) == (solutions > 0)
    assert memory.get(0, 0) == max((i + 1 for i, a in enumerate(schedule) if not a), default=0)

    # Vector-valued ANF coefficients by the Boolean subset Möbius transform.
    anf = schedule.copy()
    for i in range(d):
        for mask in range(steps):
            if mask & (1 << i):
                anf[mask] ^= anf[mask ^ (1 << i)]
    assert all(not a or mask.bit_count() <= 2 for mask, a in enumerate(anf))
    counters["SAT files" if solutions else "UNSAT files"] += 1
    counters["write rows"] += steps
    counters["zero hits"] += matches
    counters["physical DIMACS bits"] += len(raw) * 8


def main():
    counters = Counter()
    rng = Random(272606)
    signs = list(product((1, -1), repeat=3))
    for included in product((False, True), repeat=8):
        clauses = [tuple(sign * i for i, sign in enumerate(s, 1))
                   for s, yes in zip(signs, included, strict=True) if yes]
        scatter(dimacs_file(clauses, 3), counters)
    for _ in range(80):
        v = rng.randint(3, 6)
        supports = list(combinations(range(1, v + 1), 3))
        clauses = [tuple(var * rng.choice((-1, 1)) for var in rng.choice(supports))
                   for _ in range(rng.randint(1, 6))]
        scatter(dimacs_file(clauses, v), counters)
    for d in range(1, 8):
        for _ in range(60):
            rows = [(rng.randrange(1 << d), rng.randrange(2)) for _ in range(rng.randrange(d + 2))]
            good = [x for x in range(1 << d)
                    if all((x & mask).bit_count() % 2 == val for mask, val in rows)]
            for cutoff in range(1 + (1 << d)):
                actual = predecessor(rows, cutoff, d)
                assert actual == max((i for i in good if i < cutoff), default=None)
                counters["affine cutoffs"] += 1
    print(dict(sorted(counters.items())))


if __name__ == "__main__":
    main()
