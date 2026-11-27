"""Finite checks for the mirror-path CNFs and the random projection test."""

from itertools import product


def mirror_clauses(switches):
    """Variables are indexed by (layer, track), with positive integer names."""
    middle = len(switches)
    steps = switches + switches[::-1]

    def var(layer, track):
        return 1 + 2 * layer + track

    start, end = var(0, 0), var(len(steps), 0)
    clauses = [(start, start), (-end, -end)]
    for layer, switch in enumerate(steps, start=1):
        for track in (0, 1):
            destination = track ^ switch
            literal = var(layer, destination)
            if layer == middle and destination == 1:
                literal = -literal
            clauses.append((-var(layer - 1, track), literal))
    return clauses, 2 * (len(steps) + 1)


def satisfiable_2cnf(clauses, variables):
    """A variable and its negation cannot be mutually reachable."""
    edges = {v: [] for i in range(1, variables + 1) for v in (i, -i)}
    for left, right in clauses:
        edges[-left].append(right)
        edges[-right].append(left)

    def reaches(start, target):
        seen = {start}
        stack = [start]
        while stack:
            for nxt in edges[stack.pop()]:
                if nxt == target:
                    return True
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        return False

    return all(not (reaches(v, -v) and reaches(-v, v))
               for v in range(1, variables + 1))


def brute_cnf(clauses, variables):
    for values in product((False, True), repeat=variables):
        def literal(v):
            return values[abs(v) - 1] == (v > 0)
        if all(literal(left) or literal(right) for left, right in clauses):
            return True
    return False


def check_paths():
    totals = [0, 0]
    brute_checks = 0
    for length in range(1, 10):
        for switches in product((0, 1), repeat=length):
            clauses, variables = mirror_clauses(switches)
            answer = satisfiable_2cnf(clauses, variables)
            assert answer == (sum(switches) % 2 == 1), switches
            if length <= 2:
                assert brute_cnf(clauses, variables) == answer, switches
                brute_checks += 1
            totals[answer] += 1
    print(f"mirror widths 1..9: UNSAT={totals[0]} SAT={totals[1]} "
          f"direct truth-table cross-checks={brute_checks}")


def vectors(p, dim):
    return tuple(product(range(p), repeat=dim))


def linear_combination(coeffs, columns, dim, p):
    return tuple(sum(a * col[j] for a, col in zip(coeffs, columns)) % p
                 for j in range(dim))


def span(basis, dim, p):
    return frozenset(linear_combination(c, basis, dim, p)
                     for c in product(range(p), repeat=len(basis)))


def dot(left, right, p):
    return sum(a * b for a, b in zip(left, right)) % p


def independent_annihilators(image_basis, target, k, p):
    """Lexicographically first increasing independent sequence in the annihilator."""
    dim = len(target[0])
    chosen = []
    generated = span(chosen, dim, p)
    for normal in target:
        if normal in generated or any(dot(normal, col, p) for col in image_basis):
            continue
        chosen.append(normal)
        if len(chosen) == k:
            return tuple(chosen)
        generated = span(chosen, dim, p)
    raise AssertionError("annihilator has insufficient dimension")


def check_flats(p, source_dim, k):
    # b=1, so the zero space and the distinct lines exhaust all allowed columns.
    target_dim = 1 + k
    source, target = vectors(p, source_dim), vectors(p, target_dim)
    spaces = {span((), source_dim, p): ()}
    for v in source:
        spaces.setdefault(span((v,), source_dim, p), (v,))
    rejects = {(space, point): 0 for space in spaces for point in source}
    maps = 0
    for matrix in product(target, repeat=source_dim):
        maps += 1
        image = {x: linear_combination(x, matrix, target_dim, p) for x in source}
        for space, basis in spaces.items():
            tests = independent_annihilators([image[v] for v in basis], target, k, p)
            for point in source:
                if any(dot(normal, image[point], p) for normal in tests):
                    rejects[space, point] += 1

    member_checks = nonmember_checks = nonmember_rejects = 0
    for (space, point), count in rejects.items():
        if point in space:
            assert count == 0, (space, point, count)
            member_checks += maps
        else:
            assert count * (p ** k) == maps * (p ** k - 1), (space, point, count)
            nonmember_checks += maps
            nonmember_rejects += count
    print(f"F_{p}^{source_dim} -> F_{p}^{target_dim}, b=1 k={k}: "
          f"maps={maps} spaces={len(spaces)} all-member-passes={member_checks} "
          f"nonmember-rejects={nonmember_rejects}/{nonmember_checks} "
          f"for each of {nonmember_checks // maps} nonmember pairs")


if __name__ == "__main__":
    check_paths()
    check_flats(p=2, source_dim=3, k=2)
    check_flats(p=3, source_dim=2, k=1)
