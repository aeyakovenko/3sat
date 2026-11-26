"""Check local affine hulls directly from proper DIMACS on small implication cycles."""

from functools import lru_cache
from itertools import combinations
from math import comb


def dimacs(r, target):
    n = 3 * r
    rows = []
    for i in range(n):
        base = [-(i + 1), (i + 1) % n + 1]
        pad = (i + 2) % n + 1
        rows.extend([base + [pad], base + [-pad]])
    rows.append([-1, -(r + 1), -(2 * r + 1)])
    lines = [f"p cnf {n} {len(rows)}"]
    for row in rows:
        shifted = [-x if target >> (abs(x) - 1) & 1 else x for x in row]
        lines.append(" ".join(map(str, shifted)) + " 0")
    return ("\n".join(lines) + "\n").encode("ascii")


def parse(data):
    header, *lines = data.decode("ascii").splitlines()
    prefix, kind, names, count = header.split()
    assert (prefix, kind) == ("p", "cnf")
    n = int(names)
    clauses = []
    for line in lines:
        a, b, c, end = map(int, line.split())
        assert end == 0
        row = (a, b, c)
        assert len({abs(x) for x in row}) == 3
        assert all(1 <= abs(x) <= n for x in row)
        clauses.append(row)
    assert len(clauses) == int(count)
    return n, clauses


def model_sets(n, clauses):
    masks = []
    for row in clauses:
        mask = 0
        for x in range(1 << n):
            if any(bool(x >> (abs(lit) - 1) & 1) == (lit > 0) for lit in row):
                mask |= 1 << x
        masks.append(mask)
    return masks


def affine_rank(models, n):
    """Eliminate differences from a model, including for affine translates."""
    assert models
    origin = (models & -models).bit_length() - 1
    basis = {}
    while models:
        low = models & -models
        vector = (low.bit_length() - 1) ^ origin
        models -= low
        while vector:
            pivot = vector.bit_length() - 1
            if pivot in basis:
                vector ^= basis[pivot]
            else:
                basis[pivot] = vector
                break
        if len(basis) == n:
            break
    return len(basis)


def check(r, target):
    n, rows = parse(dimacs(r, target))
    masks = model_sets(n, rows)
    universe = (1 << (1 << n)) - 1
    full = universe
    for clause in masks:
        full &= clause
    assert full == 1 << target

    tested = 0
    for subset in combinations(masks, 2 * r):
        models = universe
        for clause in subset:
            models &= clause
        assert affine_rank(models, n) == n
        tested += 1
    assert tested == comb(len(rows), 2 * r)
    return tested


def minimum_hitting_set(requirements):
    """Return a minimum mask of clauses intersecting every required mask."""
    minimal = []
    for mask in sorted(set(requirements), key=lambda m: (m.bit_count(), m)):
        assert mask
        if not any(other & mask == other for other in minimal):
            minimal.append(mask)

    @lru_cache(maxsize=None)
    def solve(remaining):
        if not remaining:
            return 0
        choices = remaining[0]
        best = None
        while choices:
            clause = choices & -choices
            choices -= clause
            tail = tuple(mask for mask in remaining if not mask & clause)
            witness = clause | solve(tail)
            if best is None or witness.bit_count() < best.bit_count():
                best = witness
        return best

    return solve(tuple(minimal))


def minimum_affine_support(r):
    """For the zero target only homogeneous equations can be consequences."""
    n, rows = parse(dimacs(r, 0))
    masks = model_sets(n, rows)
    violations = [
        sum(1 << i for i, valid in enumerate(masks) if not (valid >> x) & 1)
        for x in range(1 << n)
    ]
    smallest = len(rows)
    attainers = 0
    for coeff in range(1, 1 << n):
        odd = [x for x in range(1 << n) if (x & coeff).bit_count() % 2]
        chosen = minimum_hitting_set(violations[x] for x in odd)
        assert all(violations[x] & chosen for x in odd)
        size = chosen.bit_count()
        if size < smallest:
            smallest = size
            attainers = 0
        attainers += size == smallest
    return smallest, attainers


if __name__ == "__main__":
    for r in (2, 3):
        n = 3 * r
        for target in (0, (1 << n) - 1):
            count = check(r, target)
            print(f"{n} variables, target {target:0{n}b}, {count} subsets of {2*r} span")
        smallest, attainers = minimum_affine_support(r)
        assert smallest == 2*r + 3
        print(f"{n} variables, minimum {smallest} clauses, {attainers} attaining equations")
