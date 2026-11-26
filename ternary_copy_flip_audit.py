"""Exhaust all aligned ternary table pairs and solve the two tight pebble examples."""

from collections import Counter, defaultdict, deque
from itertools import combinations, product


def translated(table, shift):
    return sum(1 << (row ^ shift) for row in range(8) if table >> row & 1)


def parity_equations(rows):
    """Pins are represented by (i, None, bit). Return None for an empty relation."""
    if not rows:
        return None
    equations = []
    for i in range(3):
        bits = {r >> i & 1 for r in rows}
        if len(bits) == 1:
            equations.append((i, None, bits.pop()))
    for i, j in combinations(range(3), 2):
        parities = {((r >> i) ^ (r >> j)) & 1 for r in rows}
        if len(parities) == 1:
            equations.append((i, j, parities.pop()))
    return equations


def accepts(row, equations):
    return equations is not None and all(
        ((row >> i & 1) ^ (0 if j is None else row >> j & 1)) == bit
        for i, j, bit in equations)


def classify():
    by_dimension = Counter()
    exceptions = set()
    linear_relations = set()
    matched = 0
    for left in range(256):
        orbits = defaultdict(list)
        for shift in range(8):
            orbits[translated(left, shift)].append(shift)
        by_dimension[len(orbits[left]).bit_length() - 1] += 1
        for right in range(256):
            shifts = tuple(orbits.get(right, ()))
            matched += bool(shifts)
            equations = parity_equations(shifts)
            reconstructed = tuple(x for x in range(8) if accepts(x, equations))
            if reconstructed == shifts:
                linear_relations.add(shifts)
            else:
                exceptions.add((left, right))
    parity = sum(1 << x for x in range(8) if x.bit_count() % 2)
    assert exceptions == set(product((parity, parity ^ 255), repeat=2))
    assert by_dimension == {0: 184, 1: 56, 2: 14, 3: 2}
    assert matched == 1726 and len(linear_relations) == 50
    return linear_relations


def graph_satisfiable(constraints):
    neighbors = defaultdict(list)
    for scope, rows in constraints:
        equations = parity_equations(rows)
        if equations is None:
            return False
        for i, j, bit in equations:
            x = scope[i]
            y = None if j is None else scope[j]
            neighbors[x].append((y, bit))
            neighbors[y].append((x, bit))
    potential = {}
    for root in neighbors:
        if root in potential:
            continue
        potential[root] = 0
        queue = deque([root])
        while queue:
            x = queue.popleft()
            for y, bit in neighbors[x]:
                value = potential[x] ^ bit
                if y in potential:
                    if potential[y] != value:
                        return False
                else:
                    potential[y] = value
                    queue.append(y)
    return True


def check_systems(relations):
    count = 0
    for second in ((1, 2, 3), (2, 2, 0)):
        for r, s in product(relations, repeat=2):
            constraints = (((0, 1, 2), r), (second, s))
            brute = any(all(sum(bits[x] << i for i, x in enumerate(scope)) in rows
                            for scope, rows in constraints)
                        for bits in product(range(2), repeat=4))
            assert brute == graph_satisfiable(constraints)
            count += 1
    return count


def duplicator_wins(domains, constraints, k):
    """Greatest family of partial homomorphisms closed under forgetting and extension."""
    names = range(len(domains))
    positions = set()
    for size in range(k + 1):
        for scope in combinations(names, size):
            for image in product(*(domains[x] for x in scope)):
                mapping = dict(zip(scope, image))
                if all(not all(x in mapping for x in atom)
                       or tuple(mapping[x] for x in atom) in allowed
                       for atom, allowed in constraints):
                    positions.add(tuple(zip(scope, image)))
    while True:
        kept = set()
        for p in positions:
            if any(p[:i] + p[i + 1:] not in positions for i in range(len(p))):
                continue
            occupied = dict(p)
            if len(p) < k and any(
                all(tuple(sorted(p + ((x, a),))) not in positions for a in domains[x])
                for x in names if x not in occupied
            ):
                continue
            kept.add(p)
        if kept == positions:
            return () in kept
        positions = kept


def check_pebbles():
    triples = ((0, 1, 3), (1, 2, 4), (2, 0, 5))
    bits = (0, 1)
    allowed = {t for t in product(bits, repeat=3) if t[0] != t[1] and t[2] == t[0]}
    nae = 255 ^ 1 ^ (1 << 7)
    shifted = translated(nae, 2)
    assert allowed == {tuple((g >> i) & 1 for i in range(3))
                       for g in range(8) if translated(nae, g) == shifted}
    variable_domains = [bits] * 6
    variable_constraints = [(triple, allowed) for triple in triples]
    # Tagged tuple-domain nodes for each incidence relation. Their numeric
    # labels are separate from the two values used for variable vertices.
    tuples = tuple(sorted(allowed))
    tuple_ids = tuple(range(2, 2 + len(tuples)))
    incidence_domains = variable_domains + [tuple_ids] * 3
    incidence_constraints = []
    for e, triple in enumerate(triples, start=6):
        for port, x in enumerate(triple):
            compatible = {(tid, t[port]) for tid, t in zip(tuple_ids, tuples)}
            incidence_constraints.append(((e, x), compatible))
    for domains, constraints in ((variable_domains, variable_constraints),
                                 (incidence_domains, incidence_constraints)):
        assert duplicator_wins(domains, constraints, 2)
        assert not duplicator_wins(domains, constraints, 3)


if __name__ == '__main__':
    rels = classify()
    n = check_systems(rels)
    check_pebbles()
    print(f'65,536 pairs, 1,726 matched, 4 proper parity exceptions; '
          f'{n:,} signed-graph checks; 2/3-pebble thresholds pass in both encodings')
