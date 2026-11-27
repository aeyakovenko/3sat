"""Build cubic Tseitin formulas and their one-literal-per-vertex SAT perturbations.

The finite integration checks use pycosat, an interface to PicoSAT.
"""
from dataclasses import dataclass, replace
from itertools import product
from random import Random

import pycosat


@dataclass(frozen=True)
class Gate:
    output: int
    inputs: tuple
    use_or: bool = False
    negate_result: bool = False

    def accepts(self, bits):
        x, y = (bool(bits[slot]) ^ inverted for slot, inverted in self.inputs)
        result = (x or y) if self.use_or else (x and y)
        return bool(bits[self.output]) == (result ^ self.negate_result)

    def reversed(self):
        swap = (2, 1, 0)
        return Gate(swap[self.output], tuple((swap[s], f) for s, f in self.inputs),
                    self.use_or, self.negate_result)


def forward(use_or=False, negate_chord=False):
    return Gate(2, ((0, False), (1, negate_chord)), use_or)


def local_form(gate):
    tuples = set(product((0, 1), repeat=3))
    allowed = {row for row in tuples if gate.accepts(row)}
    charge, = [q for q in (0, 1) if sum(sum(row) % 2 == q for row in allowed) == 3]
    parity = {row for row in tuples if sum(row) % 2 == charge}
    old, = allowed - parity
    new, = parity - allowed
    assert sum(a != b for a, b in zip(old, new)) == 1
    assert old[gate.output] != new[gate.output]
    return charge, [(row, new if row == old else row) for row in sorted(tuples - parity)]


def build(source, extra_clean=0):
    names = sorted({abs(lit) for row in source for lit in row})
    assert source and all(len(row) == len({abs(x) for x in row}) == 3 for row in source)
    sites = []
    switch = None

    def append_reset(reverse=False):
        nonlocal switch
        start = len(sites)
        gates = [forward(), forward(), forward(negate_chord=True), forward()]
        labels = [('reset', start, 0), ('reset', start, 1)] * 2
        if reverse:
            gates[-1] = replace(gates[-1], negate_result=True)
            sites.extend((gate.reversed(), label) for gate, label in reversed(list(zip(gates, labels))))
        else:
            sites.extend(zip(gates, labels))
            switch = start + 3

    occurrences = {x: [] for x in names}
    for row, clause in enumerate(source):
        for pos, lit in enumerate(clause):
            occurrences[abs(lit)].append((lit < 0, ('occ', row, pos)))
    for x in names:
        append_reset()
        for negative, label in sorted(occurrences[x]):
            gate = forward(negate_chord=True).reversed() if negative else forward(use_or=True)
            sites.append((gate, label))
    for row in range(len(source)):
        append_reset()
        for pos in range(3):
            sites.append((forward(use_or=True), ('occ', row, pos)))
        append_reset(reverse=True)

    if sum(local_form(g)[0] for g, _ in sites) % 2 == 0:
        gate, label = sites[switch]
        sites[switch] = (forward(negate_chord=True), label)
        assert gate == forward()

    for i in range(extra_clean):
        labels = [('clean', i, 0), ('clean', i, 1)] * 2
        sites.extend((None, label) for label in labels)
    size = len(sites)
    matching = {}
    for j, (_, label) in enumerate(sites):
        matching.setdefault(label, []).append(j)
    assert all(len(pair) == 2 and 1 < abs(pair[0] - pair[1]) < size - 1
               for pair in matching.values())
    chord_index = {label: size + i + 1 for i, label in enumerate(matching)}

    def clause(row, edges):
        return tuple(-e if value else e for value, e in zip(row, edges))

    base, edited, charges = [], [], []
    for i, (gate, label) in enumerate(sites):
        edges = ((i-1) % size + 1, chord_index[label], i+1)
        assert len(set(edges)) == 3
        if gate is None:
            q = 0
            changes = [(row, row) for row in product((0, 1), repeat=3) if sum(row) % 2]
        else:
            q, changes = local_form(gate)
        charges.append(q)
        for old, new in changes:
            base.append(clause(old, edges))
            edited.append(clause(new, edges))
    assert sum(charges) % 2 == 1
    assert len(base) == 4*size and size == 4*len(names) + 14*len(source) + 4*extra_clean
    assert all(sum(x != y for x, y in zip(a, b)) <= 1 for a, b in zip(base, edited))
    changed = [sum(a != b for a, b in zip(base[i:i+4], edited[i:i+4])) for i in range(0, len(base), 4)]
    assert changed == [1] * (size - 4*extra_clean) + [0] * (4*extra_clean)
    return base, edited


def satisfiable(clauses):
    answer = pycosat.solve(clauses, prop_limit=500000)
    if answer == 'UNKNOWN':
        raise RuntimeError('PicoSAT reached the check budget')
    return answer != 'UNSAT'


def audit():
    triples = list(product((False, True), repeat=3))
    clauses = [tuple(-i if b else i for i, b in enumerate(bits, 1)) for bits in triples]
    families = [[c for i, c in enumerate(clauses) if subset >> i & 1] for subset in range(1, 256)]
    rng = Random(20261125)
    for _ in range(55):
        n = rng.randrange(3, 9)
        rows = [tuple(i if rng.getrandbits(1) else -i for i in rng.sample(range(1, n+1), 3))
                for _ in range(rng.randrange(2, 10))]
        families.append(rows)
    deletions = 0
    for i, rows in enumerate(families):
        base, edited = build(rows, extra_clean=i % 3)
        if i in (0, 1, 6):
            assert not satisfiable(base)
        assert satisfiable(edited) == satisfiable(rows)
        if i in (0, 1, 6):
            for k in range(len(base)):
                assert satisfiable(base[:k] + base[k+1:])
                deletions += 1
    print(f'{len(families)} cubic SAT reductions; {deletions} single-clause deletions of odd references')


if __name__ == '__main__':
    audit()
