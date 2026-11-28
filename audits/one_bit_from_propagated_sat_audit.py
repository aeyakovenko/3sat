"""Audit the model bijection after one physical bit changes in proper DIMACS.

Run with pycosat installed. The companion audit supplies its original circuit
constructor and generic support-mask/propagation solver. Python dictionaries
check the construction; the native complexity argument uses deterministic tries.
"""
from itertools import product
from random import Random

import pycosat

from ordinary_circuit_face_audit import dumps, formula, propagate


def build_pair(source):
    normalized = sorted({tuple(sorted(clause, key=abs)) for clause in source})
    names = sorted({abs(lit) for clause in normalized for lit in clause})
    m = len(normalized)
    k = max(1, (len(names) + m + 7) // 8)
    rails = [(10 * (i + 1) + 2, 10 * (i + 1) + 3) for i in range(k)]
    a, b, c = (10 * k + i for i in (4, 5, 6))
    p = rails[0][1]
    reserved = {v for pair in rails for v in pair} | {a, b, c}
    fillers = [v for v in range(1, c + 1) if v not in reserved]
    old = dict(zip(names, fillers))
    aux = fillers[len(names):len(names) + m]
    assert len(aux) == m
    base = formula([1] * k, [])
    additions = [(a, p, b), (a, p, -b), (-a, -p, b), (-a, -p, -b)]
    ports = set(old.values()).union(aux, (a, b, c, p))
    positive = {one for _, one in rails}
    for v in range(1, c + 1):
        if v not in ports:
            additions.append((v if v in positive else -v, b, c))
    for clause, t in zip(normalized, aux):
        u, v, w = [old[abs(lit)] if lit > 0 else -old[-lit] for lit in clause]
        additions.extend([(-a, u, t), (-t, a, b), (-t, -u, b), (-t, v, w)])
    closed = base + additions
    opened = closed.copy()
    edge = opened.index((-a, b, c))
    opened[edge] = (-p, b, c)
    permutation = {a: 2, 2: a, p: 3, 3: p}

    def renumber(lit):
        return permutation.get(abs(lit), abs(lit)) * (1 if lit > 0 else -1)

    def rename(clauses):
        return [tuple(renumber(lit) for lit in clause) for clause in clauses]

    return rename(closed), rename(opened), {name: renumber(v) for name, v in old.items()}


def chunk_literals(clause, limit):
    pending, length = [], 0
    for lit in clause:
        size = len(str(lit)) + 1
        if pending and length + size > limit:
            yield tuple(pending)
            pending, length = [], 0
        if size > limit:
            yield (lit,)
        else:
            pending.append(lit)
            length += size
    if pending:
        yield tuple(pending)


def properize(source, limit):
    names = sorted({abs(lit) for clause in source for lit in clause})
    ports = {name: i + 1 for i, name in enumerate(names)}
    a, b, c = (len(names) + i for i in (1, 2, 3))
    # Three false constants, uniquely determined by seven rows.
    clauses = [tuple(-v if bit else v for v, bit in zip((a, b, c), mask))
               for mask in product((0, 1), repeat=3) if any(mask)]
    clauses.extend((v, -a, b) for v in ports.values())
    last = c

    def or_gate(u, v):
        nonlocal last
        if u == v:
            return u
        if u == -v:
            return -a
        # Constants may occur after a tautological subdisjunction.
        if u == -a or v == -a:
            return -a
        last += 1
        clauses.extend([(-u, last, a), (-v, last, a), (u, v, -last)])
        return last

    def fold(parts):
        result = parts[0]
        for part in parts[1:]:
            result = or_gate(result, part)
        return result

    shared = {}
    for clause in dict.fromkeys(tuple(ch) for ch in source):
        outputs = []
        for chunk in chunk_literals(clause, limit):
            if chunk not in shared:
                shared[chunk] = fold([ports[abs(lit)] if lit > 0 else -ports[-lit]
                                      for lit in chunk])
            outputs.append(shared[chunk])
        if not outputs:
            clauses.append((a, b, c))
        else:
            result = fold(outputs)
            if result != -a:
                clauses.append((result, a, b))
    return clauses, ports


def source_models(source, names):
    models = set()
    for bits in product((False, True), repeat=len(names)):
        assignment = dict(zip(names, bits))
        if all(any(assignment[abs(lit)] == (lit > 0) for lit in clause) for clause in source):
            models.add(bits)
    return models


def check(source, block=None):
    if block is None:
        proper = source
        original = {abs(lit): abs(lit) for clause in source for lit in clause}
    else:
        proper, original = properize(source, block)
    closed, opened, projected = build_pair(proper)
    ports = {name: projected[v] for name, v in original.items()}
    cfile, ofile = dumps(closed), dumps(opened)
    assert len(cfile) == len(ofile)
    assert sum((a ^ b).bit_count() for a, b in zip(cfile, ofile)) == 1
    assert all(len({abs(lit) for lit in clause}) == 3 for clause in closed + opened)
    assert propagate(cfile) is True
    assert len(list(pycosat.itersolve(closed))) == 1
    wanted = source_models(source, list(ports))
    models = list(pycosat.itersolve(opened))
    got = {tuple(port in model for port in ports.values()) for model in models}
    assert len(models) == len(got) and got == wanted
    return len(wanted)


if __name__ == '__main__':
    patterns = list(product(*[(i, -i) for i in (1, 2, 3)]))
    counts = [check([clause for j, clause in enumerate(patterns) if mask & (1 << j)])
              for mask in range(256)]
    rng = Random(251128)
    for _ in range(144):
        n = rng.randint(3, 6)
        source = [tuple(rng.choice((v, -v)) for v in rng.sample(range(1, n + 1), 3))
                  for _ in range(rng.randrange(1, 48))]
        if rng.choice((0, 1)):
            source += list(reversed(source))
        counts.append(check(source))
    print(f'{len(counts)} proper pairs, {sum(counts)} models in bijection, '
          f'{counts.count(0)} edited UNSAT')

    wide = []
    sparse = [3, 12345678901234567890123, 81, 1, 7]
    cases = [[], [()], [(1, -1, 2, 3)], [(1, 2), (-1,), ()],
             [tuple(sparse), tuple(sparse), tuple(reversed(sparse))]]
    for _ in range(75):
        candidates = [tuple(rng.choice((v, -v)) for v in rng.choices(sparse, k=rng.randrange(1, 12)))
                      for _ in range(rng.randrange(1, 9))]
        cases.append(candidates + list(reversed(candidates[:3])))
    for source in cases:
        for block in (2, 7, 17):
            wide.append(check(source, block))
    print(f'{len(wide)} unbounded-width/chunk-size pairs, {sum(wide)} models in bijection, '
          f'{wide.count(0)} edited UNSAT')
