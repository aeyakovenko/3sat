"""Recover an unlabeled doubled Tseitin system from the sparse proper DIMACS layout."""

from collections import defaultdict
from itertools import combinations, product
from random import Random

from sparse_incidence_dimacs_audit import parse, relabel, serialize


def decode(text):
    """Return the SAT verdict on a recognized layout, or None when the fast path declines."""
    try:
        names, clauses = parse(text)
    except (AssertionError, ValueError):
        return None
    d = names - 3
    a, b, c = d + 1, d + 2, d + 3
    pin = tuple(tuple(-x if bit else x for x, bit in zip((a, b, c), bits))
                for bits in product((0, 1), repeat=3) if any(bits))
    if clauses[:7] != pin or len(clauses) != 2 * d + 7:
        return None
    if any(row != (i, -a, b) for i, row in enumerate(clauses[7:7 + d], 1)):
        return None
    raw = [row for row in clauses[7 + d:] if row != (-a, b, c)]
    if any(abs(x) > d for row in raw for x in row):
        return None
    return decode_rows(raw)


def decode_rows(clauses):
    """Rows have already been parsed as proper triples; their order is arbitrary."""
    buckets = defaultdict(list)
    for row in clauses:
        ordered = sorted(row, key=abs)
        key = tuple(map(abs, ordered))
        mask = sum((x < 0) << i for i, x in enumerate(ordered))
        buckets[key].append(mask)

    equations = {}
    partners = defaultdict(set)
    for variables, masks in buckets.items():
        parities = {m.bit_count() % 2 for m in masks}
        if len(masks) != 4 or len(set(masks)) != 4 or len(parities) != 1:
            return None
        equations[variables] = 1 - parities.pop()
        x, y, z = variables
        for pair, third in [((x, y), z), ((x, z), y), ((y, z), x)]:
            partners[pair].add(third)

    mate = {}
    for twins in partners.values():
        if len(twins) != 2:
            return None
        x, y = twins
        if mate.get(x, y) != y or mate.get(y, x) != x:
            return None
        mate[x], mate[y] = y, x
    quotient = defaultdict(dict)
    for variables, charge in equations.items():
        items = sorted((min(x, mate[x]), int(x > mate[x])) for x in variables)
        triple, choice = zip(*items)
        if len(set(triple)) != 3 or choice in quotient[triple]:
            return None
        quotient[triple][choice] = charge ^ (sum(choice) % 2)

    charges = []
    ends = defaultdict(list)
    for triple, choices in quotient.items():
        if len(choices) != 8 or len(set(choices.values())) != 1:
            return None
        for edge in triple:
            ends[edge].append(len(charges))
        charges.append(next(iter(choices.values())))
    adj = [[] for _ in charges]
    for vertices in ends.values():
        if len(vertices) != 2:
            return None
        u, v = vertices
        adj[u].append(v)
        adj[v].append(u)
    visited = set()
    for start in range(len(adj)):
        if start in visited:
            continue
        visited.add(start)
        todo = [start]
        parity = 0
        while todo:
            u = todo.pop()
            parity ^= charges[u]
            for v in adj[u]:
                if v not in visited:
                    visited.add(v)
                    todo.append(v)
        if parity:
            return False
    return True


def local_connected_verdict(variables, rows, rounds):
    """Audit fixed 32-slot incidence lanes, synchronous rounds and two payload banks.

    The outer arrays are indexed by public row or literal-name positions. Local
    sets and dictionaries below have at most 64 source rows. This Python witness
    checks the mathematical decoder, not Python instruction-level support.
    """
    if variables <= 0 or not rows or 3 * len(rows) != 32 * variables:
        return None
    occurrences = [[] for _ in range(variables + 1)]
    triples = [tuple(sorted(map(abs, row))) for row in rows]
    for i, (x, y, z) in enumerate(triples):
        if not 1 <= x < y < z <= variables:
            return None
        for u in (x, y, z):
            if len(occurrences[u]) == 32:
                return None
            occurrences[u].append(i)
    if any(len(lane) != 32 for lane in occurrences[1:]):
        return None

    # One co-occurring pair is enough to discover the other copy. All proposed
    # pairings and actual lifted constraints are subsequently checked locally.
    mate = [0] * (variables + 1)
    for u in range(1, variables + 1):
        x, y = [v for v in triples[occurrences[u][0]] if v != u]
        others = {v for i in occurrences[x] if y in triples[i]
                  for v in triples[i] if v != x and v != y}
        if len(others) != 2 or u not in others:
            return None
        mate[u] = next(v for v in others if v != u)
    if any(mate[mate[u]] != u for u in range(1, variables + 1)):
        return None

    keys = [tuple(sorted(min(u, mate[u]) for u in t)) for t in triples]
    owner = [0] * len(rows)
    charges = [0] * len(rows)
    for i, key in enumerate(keys):
        if len(set(key)) != 3:
            return None
        first = key[0]
        candidates = occurrences[first] + occurrences[mate[first]]
        group = [j for j in candidates if keys[j] == key]
        owner[i] = min(group)
        if i != owner[i]:
            continue
        if len(group) != 32:
            return None
        forbidden = set()
        normalized = set()
        for j in group:
            ordered = sorted(rows[j], key=lambda lit: min(abs(lit), mate[abs(lit)]))
            copy = tuple(int(abs(lit) > mate[abs(lit)]) for lit in ordered)
            signs = tuple(int(lit < 0) for lit in ordered)
            forbidden.add((copy, signs))
            normalized.add(1 ^ ((sum(signs) + sum(copy)) % 2))
        if len(forbidden) != 32 or len(normalized) != 1:
            return None
        charges[i] = normalized.pop()

    ends = [None] * (variables + 1)
    for u in range(1, variables + 1):
        endpoints = {owner[i] for i in occurrences[u]}
        if len(endpoints) != 2:
            return None
        ends[u] = tuple(endpoints)
    adj = [[] for _ in rows]
    for i, key in enumerate(keys):
        if i == owner[i]:
            for u in key:
                a, b = ends[u]
                if i != a and i != b:
                    return None
                adj[i].append(b if i == a else a)

    reached = [i == owner[0] for i in range(len(rows))]
    for _ in range(rounds):
        reached = [old or any(reached[j] for j in adj[i]) for i, old in enumerate(reached)]
    if any(not reached[i] for i in range(len(rows)) if i == owner[i]):
        return None
    bank = [False, True]
    for charge in charges:
        bank = [bank[j ^ charge] for j in range(2)]
    return not bank[0]


def lifted_rows(edges, charges):
    incident = [[] for _ in charges]
    for edge, (u, v) in enumerate(edges):
        incident[u].append(edge)
        incident[v].append(edge)
    assert all(len(t) == len(set(t)) == 3 for t in incident)
    rows = [None] * (2 * len(edges))
    for triple, charge in zip(incident, charges):
        for choice in product((0, 1), repeat=3):
            variables = [1 + 2 * edge + bit for edge, bit in zip(triple, choice)]
            rhs = (charge + sum(choice)) % 2
            for bits in product((0, 1), repeat=3):
                if sum(bits) % 2 != rhs:
                    rows.append(tuple(-x if bit else x for x, bit in zip(variables, bits)))
    return rows


def main():
    import pycosat
    rng = Random(261127)
    k4 = list(combinations(range(4), 2))
    k33 = [(u, v) for u in range(3) for v in range(3, 6)]
    separate = k4 + [(u + 4, v + 4) for u, v in k4]
    checked = rejected = raw_checked = raw_rejected = 0
    local_decided = local_disconnected = 0
    for edges, sizes in [(k4, [4]), (k33, [6]), (separate, [4, 4])]:
        for _ in range(12):
            charges = [rng.randrange(2) for _ in range(sum(sizes))]
            expected = all(sum(charges[sum(sizes[:i]):sum(sizes[:i + 1])]) % 2 == 0
                           for i in range(len(sizes)))
            rows = lifted_rows(edges, charges)
            variable_count = 2 * len(edges)
            variable_perm = list(range(1, variable_count + 1))
            rng.shuffle(variable_perm)
            raw = []
            for source in rows[variable_count:]:
                triple = [(1 if x > 0 else -1) * variable_perm[abs(x) - 1] for x in source]
                rng.shuffle(triple)
                raw.append(triple)
            rng.shuffle(raw)
            for alteration in (False, True):
                changed = [t.copy() for t in raw]
                if alteration:
                    changed[0][0] = -changed[0][0]
                lines = [f'p cnf {variable_count} {len(changed)}\n']
                lines.extend(f'{x} {y} {z} 0\n' for x, y, z in changed)
                _, triples = parse(''.join(lines).encode('ascii'))
                observed = decode_rows(triples)
                local = local_connected_verdict(variable_count, triples, variable_count.bit_length())
                if alteration:
                    assert observed is None and local is None
                    raw_rejected += 1
                else:
                    result = pycosat.solve(triples)
                    assert result != 'UNKNOWN' and observed is expected and (result != 'UNSAT') == expected
                    if len(sizes) == 1:
                        assert local is expected
                        assert local_connected_verdict(variable_count, triples, 0) is None
                        local_decided += 1
                    else:
                        assert local is None
                        local_disconnected += 1
                    raw_checked += 1
            perm = list(range(1, len(rows) + 1))
            rng.shuffle(perm)
            moved = relabel(rows, [0] + perm)
            for alteration in (False, True):
                sample = list(moved)
                if alteration:
                    i = next(i for i, row in enumerate(sample) if row is not None)
                    x, y, z = sample[i]
                    sample[i] = (-x, y, z)
                text, _ = serialize(sample)
                verdict = decode(text)
                if alteration:
                    assert verdict is None
                    rejected += 1
                else:
                    _, clauses = parse(text)
                    result = pycosat.solve(clauses)
                    assert result != 'UNKNOWN' and verdict is expected and (result != 'UNSAT') == expected
                    checked += 1
    print(f'{checked} sparse files and {raw_checked} permuted raw files agreed with PicoSAT; '
          f'{rejected + raw_rejected} one-sign corruptions left the fast path')
    print(f'Local BFS and copy: {local_decided} connected verdicts, '
          f'{local_disconnected} disconnected and {raw_rejected} corrupted files declined')


if __name__ == '__main__':
    main()
