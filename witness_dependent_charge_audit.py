"""Finite checks for witness-dependent Z/6 charges. Uses the Python standard library."""

from itertools import product


def graph(side):
    """Outgoing arcs in generator order +1,...,+5,-1,...,-5."""
    adjacency = []
    for x, y, sheet in product(range(side), range(side), range(13)):
        neighbors = []
        for sign in (1, -1):
            shears = [(x + sign*2*y, y), (x + sign*(2*y+1), y),
                      (x, y + sign*2*x), (x, y + sign*(2*x+1)), (x, y)]
            for j, (u, v) in enumerate(shears, 1):
                dest = 13 * ((u % side)*side + v % side) + (sheet + sign*j) % 13
                neighbors.append(dest)
        adjacency.append(neighbors)
    for u, row in enumerate(adjacency):
        assert len(set(row)) == 10 and u not in row
        for j, v in enumerate(row):
            offset = j+1 if j < 5 else -(j-4)
            assert (v-u) % 13 == offset % 13
            assert adjacency[v][(j+5) % 10] == u
    return adjacency


def spanning_tree(adjacency):
    parent = {0: None}
    order = [0]
    for u in order:
        for v in adjacency[u]:
            if v not in parent:
                parent[v] = u
                order.append(v)
    assert len(parent) == len(adjacency)
    return parent, order


def tree_flow(tree, charges, modulus):
    parent, order = tree
    remaining = list(charges)
    shifts = {}
    for v in reversed(order[1:]):
        u = parent[v]
        z = remaining[v] % modulus
        shifts[v, u], shifts[u, v] = z, -z % modulus
        remaining[u] += z
    return shifts if remaining[0] % modulus == 0 else None


def check_divergence(adjacency, flow, rhs, modulus):
    for u, nbrs in enumerate(adjacency):
        values = [flow.get((u, v), 0) for v in nbrs]
        assert sum(values) % modulus == rhs[u] % modulus
        assert all((z+flow.get((v, u), 0)) % modulus == 0 for v, z in zip(nbrs, values))


def charge_shifts():
    tuples = shift_vectors = 0
    for side in (1, 5, 7):
        adjacency = graph(side)
        n = len(adjacency)
        tree = spanning_tree(adjacency)
        targets = range(n) if side == 1 else (0, 1, 7, n//2, n-1)
        for p in (2, 3):
            scale = 6//p
            for target in targets:
                rhs = [int(u == target)-1 for u in range(n)]
                shifts = tree_flow(tree, rhs, p)
                assert shifts is not None
                check_divergence(adjacency, shifts, rhs, p)
                shift_vectors += 1
                # Each possible residue shift preserves the reversal predicate.
                for shift, u, v in product(range(p), repeat=3):
                    z = scale*((u+shift) % p) + scale*((v-shift) % p)
                    assert (z % 6 == 0) == ((u+v) % p == 0)
                if side == 1 and target == 3:
                    for u in (2, 3):  # One uncharged vertex and the charged one.
                        correction = [shifts.get((u, v), 0) for v in adjacency[u]]
                        for labels in product(range(p), repeat=10):
                            out = sum(scale*((z+h) % p) for z, h in zip(labels, correction))
                            assert (sum(labels) % p == 1) == (out % 6 == scale*(u == target))
                            tuples += 1
        print(f"simple reversible graph on {n} vertices with all ten labeled offsets")
    print(f"all-one to singleton shifts {shift_vectors}; local label tuples {tuples}")


def consistent_mod(incidence, rhs, p):
    """Solve these incidence equations independently by field elimination."""
    matrix = [[z % p for z in row+[b]] for row, b in zip(incidence, rhs)]
    pivot = 0
    for j in range(len(incidence[0])):
        selected = next((i for i in range(pivot, len(matrix)) if matrix[i][j]), None)
        if selected is None:
            continue
        matrix[pivot], matrix[selected] = matrix[selected], matrix[pivot]
        inverse = pow(matrix[pivot][j], -1, p)
        basis = [z*inverse % p for z in matrix[pivot]]
        for i in range(pivot+1, len(matrix)):
            a = matrix[i][j]
            matrix[i] = [(x-a*y) % p for x, y in zip(matrix[i], basis)]
        pivot += 1
    return all(any(row[:-1]) or row[-1] == 0 for row in matrix)


def charge_verdicts():
    adjacency = graph(1)
    n = len(adjacency)
    edges = [(u, v) for u, row in enumerate(adjacency) for v in row if u < v]
    incidence = [[int(i == u)-int(i == v) for u, v in edges] for i in range(n)]
    tree = spanning_tree(adjacency)
    verdict = {}
    for target in [None, *range(n)]:
        for a in (2, 3):
            rhs = [a*int(u == target) for u in range(n)]
            by_crt = all(consistent_mod(incidence, rhs, p) for p in (2, 3))
            witness = tree_flow(tree, rhs, 6)
            assert (witness is not None) == by_crt
            if witness is not None:
                check_divergence(adjacency, witness, rhs, 6)
            verdict[target, a] = by_crt
    # The same solvers accept nonzero balanced demands.
    for a in (1, 2, 3):
        rhs = [a, -a]+[0]*(n-2)
        assert all(consistent_mod(incidence, rhs, p) for p in (2, 3))
        check_divergence(adjacency, tree_flow(tree, rhs, 6), rhs, 6)
    return verdict


def source_formulas():
    proper_clauses = [tuple(sign*i for i, sign in enumerate(signs, 1) if sign)
                      for signs in product((-1, 0, 1), repeat=3)]
    clauses = proper_clauses + [(1, 1, -2), (2, -2, 3)]
    yield ()
    yield from ((clause,) for clause in clauses)
    yield from product(clauses, repeat=2)
    all_ternary = tuple(c for c in proper_clauses if len(c) == 3)
    yield all_ternary
    for i in range(len(all_ternary)):
        yield all_ternary[:i]+all_ternary[i+1:]


def source_equivalence():
    verdicts = charge_verdicts()
    formulas = assignments = selector_checks = positives = 0
    for formula in source_formulas():
        formulas += 1
        brute_yes = coupled_yes = False
        for x in product((False, True), repeat=3):
            assignments += 1
            true_literals = {i if b else -i for i, b in enumerate(x, 1)}
            direct = all(true_literals.intersection(clause) for clause in formula)
            prefix = True
            flags = []
            for clause in formula:
                passed = any(x[abs(lit)-1] == (lit > 0) for lit in clause)
                flags.append(prefix and not passed)
                prefix = prefix and passed
            assert sum(flags) == int(not direct)
            target = flags.index(True) if any(flags) else None
            brute_yes |= direct
            for a in (2, 3):
                feasible = verdicts[target, a]
                assert feasible == direct
                coupled_yes |= feasible
                selector_checks += 1
        assert brute_yes == coupled_yes
        positives += int(coupled_yes)
    print(f"source formulas {formulas}, satisfiable {positives}, assignments {assignments}, "
          f"selector checks {selector_checks}")


if __name__ == "__main__":
    charge_shifts()
    source_equivalence()
