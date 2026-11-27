"""Finite checks for the packed output of a shallow Boolean index circuit.

Gate lists alternate OR and AND. Bottom fan-in entries are signed, one-based
variable numbers; later fan-in entries are zero-based preceding gate indices.
Each restriction stage evaluates all low physical lanes under the same tower.
"""

from collections import Counter
from itertools import combinations
from math import comb
from random import Random


class OverflowTree(Exception):
    """The canonical tree exceeds the chosen depth cutoff."""


def canonical(terms, fixed, budget):
    """A tree is a Boolean leaf or (variable, zero-subtree, one-subtree)."""
    first_free = None
    for term in terms:
        if any(v in fixed and fixed[v] != a for v, a in term):
            continue
        free = tuple(v for v, _ in term if v not in fixed)
        if not free:
            return True
        if first_free is None:
            first_free = free
    if first_free is None:
        return False
    if len(first_free) > budget:
        raise OverflowTree

    def query(position):
        if position == len(first_free):
            return canonical(terms, fixed, budget - position)
        v = first_free[position]
        branches = []
        for bit in (0, 1):
            fixed[v] = bit
            branches.append(query(position + 1))
        del fixed[v]
        return v, *branches

    return query(0)


def false_paths(tree, path=()):
    if isinstance(tree, bool):
        if not tree:
            yield path
    else:
        var, zero, one = tree
        yield from false_paths(zero, (*path, (var, 0)))
        yield from false_paths(one, (*path, (var, 1)))


def layer_trees(layers, bottom_or, tower, assignment, budget):
    targets = []
    path_lists = []
    for level, (gates, live) in enumerate(zip(layers, tower, strict=True)):
        target = bottom_or ^ bool(level & 1)
        fixed = {v: a for v, a in enumerate(assignment) if v not in live}
        roots = []
        for gate in gates:
            if level == 0:
                terms = [((abs(lit) - 1, int((lit > 0) == target)),) for lit in gate]
            else:
                terms = [term for child in gate for term in path_lists[child]]
            roots.append(canonical(terms, fixed, budget))
        path_lists = [list(false_paths(root)) for root in roots]
        targets = [(root, target) for root in roots]
    return targets


def direct(layers, bottom_or, ell, assignment):
    values = [(assignment >> v) & 1 for v in range(ell)]
    for level, gates in enumerate(layers):
        combine = any if bottom_or ^ bool(level & 1) else all
        if level == 0:
            values = [combine(bool(values[abs(x) - 1]) == (x > 0) for x in g) for g in gates]
        else:
            values = [combine(values[x] for x in g) for g in gates]
    return list(map(int, values))


def root_coefficients(tree, variable_rank, modulus):
    if isinstance(tree, bool):
        return {0: int(tree)}
    var, zero, one = tree
    left = root_coefficients(zero, variable_rank, modulus)
    right = root_coefficients(one, variable_rank, modulus)
    variable_bit = 1 << variable_rank[var]
    result = dict(left)
    for mask in left.keys() | right.keys():
        assert not mask & variable_bit
        val = (right.get(mask, 0) - left.get(mask, 0)) % modulus
        if val:
            result[mask | variable_bit] = val
    return result


def colex(mask):
    positions = [v for v in range(mask.bit_length()) if mask & (1 << v)]
    return sum(comb(v, i) for i, v in enumerate(positions, 1))


def encode_residues(values, modulus):
    """One-hot bit-slicing of fixed-modulus residues."""
    result = [0] * modulus
    for lane, value in enumerate(values):
        result[value] |= 1 << lane
    return tuple(result)


def plus(a, b):
    modulus = len(a)
    out = [0] * modulus
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[(i + j) % modulus] |= x & y
    return tuple(out)


def emit_restrictions(rows, variables, base, output, target):
    """Dense colex rows, indexed by degree; recurse on the largest variable."""
    r = len(variables)
    if not r:
        assert output[base] is None
        output[base] = rows[0][0][target]
        return
    zero, one = [], []
    for j, row in enumerate(rows):
        if j >= r:
            break
        count = comb(r - 1, j)
        without = row[:count]
        zero.append(without)
        if j + 1 < len(rows):
            with_var = rows[j + 1][comb(r - 1, j + 1):]
            assert len(with_var) == count
            one.append([plus(a, b) for a, b in zip(without, with_var, strict=True)])
        else:
            one.append(without)
    emit_restrictions(zero, variables[:-1], base, output, target)
    emit_restrictions(one, variables[:-1], base | (1 << variables[-1]), output, target)


def generate(layers, bottom_or, ell, low, tower, budget, modulus, target, counters):
    variables = sorted(tower[-1])
    rank = {v: i for i, v in enumerate(variables)}
    fixed_positions = sorted(set(range(low, ell)) - set(variables))
    nlanes = 1 << low
    words = [None] * (1 << (ell - low))
    for setting in range(1 << len(fixed_positions)):
        base = sum(((setting >> i) & 1) << v for i, v in enumerate(fixed_positions))
        lane_coefs = []
        try:
            for lane in range(nlanes):
                bits = [int(bool((base | lane) & (1 << v))) for v in range(ell)]
                roots = layer_trees(layers, bottom_or, tower, bits, budget)
                full = Counter()
                for tree, positive in roots:
                    poly = root_coefficients(tree, rank, modulus)
                    if not positive:
                        full[0] += 1
                    for key, value in poly.items():
                        full[key] += value if positive else -value
                lane_coefs.append(full)
        except OverflowTree:
            counters["fallback cofactor"] += 1
            for z in range(1 << len(variables)):
                addr = base | sum(((z >> i) & 1) << v for i, v in enumerate(variables))
                assert words[addr >> low] is None
                words[addr >> low] = sum(
                    (sum(direct(layers, bottom_or, ell, addr | lane)) % modulus == target) << lane
                    for lane in range(nlanes)
                )
            continue
        counters["switched cofactor"] += 1
        rows = []
        for j in range(min(budget, len(variables)) + 1):
            row = [None] * comb(len(variables), j)
            for indices in combinations(range(len(variables)), j):
                mask = sum(1 << i for i in indices)
                row[colex(mask)] = encode_residues([p[mask] % modulus for p in lane_coefs], modulus)
            rows.append(row)
        emit_restrictions(rows, [v - low for v in variables], base >> low, words, target)
    return words


def repack(words, logical_width, physical_width):
    output, buf, size = [], 0, 0
    for word in words:
        buf |= word << size
        size += logical_width
        if size >= physical_width:
            output.append(buf & ((1 << physical_width) - 1))
            buf >>= physical_width
            size -= physical_width
    if size:
        output.append(buf)
    return output


def check(layers, bottom_or, ell, low, tower, budget, modulus, target, counters):
    out = generate(layers, bottom_or, ell, low, tower, budget, modulus, target, counters)
    values = [int(sum(direct(layers, bottom_or, ell, i)) % modulus == target) for i in range(1 << ell)]
    expected = sum(x << i for i, x in enumerate(values))
    physical = (1 << low) + 1
    final = repack(out, 1 << low, physical)
    assert sum(w << (i * physical) for i, w in enumerate(final)) == expected
    counters["circuit/tower/residue tests"] += 1
    counters["ordinary truth bits"] += len(values)
    return expected


def main():
    rng = Random(27112026)
    counters = Counter()
    for _ in range(110):
        ell = rng.randint(4, 9)
        low = rng.randint(1, min(3, ell - 2))
        depth = rng.randint(1, 4)
        layers = []
        width = ell
        live = list(range(low, ell))
        tower = []
        for level in range(depth):
            count = rng.randint(1, 5)
            gates = []
            for _ in range(count):
                inputs = rng.choices(range(width), k=rng.randint(0, min(width + 2, 6)))
                if level == 0:
                    inputs = [rng.choice((-1, 1)) * (v + 1) for v in inputs]
                gates.append(inputs)
            layers.append(gates)
            width = count
            live = sorted(rng.sample(live, k=rng.randint(0 if level + 1 == depth else 1, len(live))))
            tower.append(set(live))
        bottom_or = rng.choice((True, False))
        for b in sorted({0, 2, ell}):
            for modulus in (2, 3, 4):
                check(layers, bottom_or, ell, low, tower, b, modulus, rng.randrange(modulus), counters)

    for dimacs in (b"p cnf 2 2\n1 -2 0\n2 0\n", b"p cnf 1 2\n1 0\n-1 0\n"):
        raw = int.from_bytes(dimacs, "little")
        ell = (len(dimacs) * 8 - 1).bit_length()
        minterms = [
            [(v + 1) * (1 if i & (1 << v) else -1) for v in range(ell)]
            for i in range(1 << ell) if raw & (1 << i)
        ]
        layers = [minterms, [list(range(len(minterms)))]]
        output = check(layers, False, ell, 2, [set(range(2, ell)), {2, ell - 1}], ell, 2, 1, counters)
        assert output.to_bytes(1 << (ell - 3), "little")[:len(dimacs)] == dimacs
    print(dict(sorted(counters.items())))


if __name__ == "__main__":
    main()
