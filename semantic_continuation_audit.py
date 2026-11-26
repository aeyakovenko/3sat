"""Enumerate physical DIMACS continuations with PicoSAT.

Install: python -m pip install pycosat==0.6.6
Run:     python semantic_continuation_audit.py
"""

from itertools import product

import pycosat


PADDING = (1, 4, 5)
SOURCE = (7, 8, 9)
PUBLIC_MODEL = frozenset((2, 6))


def signed_rows(names):
    return [tuple(sign * name for sign, name in zip(signs, names))
            for signs in product((-1, 1), repeat=3)]


def gated_negation(output, value):
    """Enforce output iff (selector 3 and not value); name 1 is false."""
    return [(-output, 3, 1), (-output, -value, 1), (output, -3, value)]


def encode(source, paired, query):
    clauses = [row for row in signed_rows(PADDING) if row != PADDING]
    clauses.extend([(2, 3, 1), (-2, -3, 1), (6, 1, 4)])
    clauses.extend((3, -name, 1) for name in SOURCE)
    for gate, (first, second, third) in enumerate(source, start=10):
        clauses.extend(gated_negation(gate, first))
        clauses.append((-gate, second, third))
    pairs = len(SOURCE) + len(source)
    if paired:
        for name in range(7, 7 + pairs):
            clauses.extend(gated_negation(name + pairs, name))
    clauses.append((query, 1, 4))
    variables = 6 + (2 if paired else 1) * pairs
    header = f"p cnf {variables} {len(clauses)}\n"
    body = "".join(f"{a} {b} {c} 0\n" for a, b, c in clauses)
    return (header + body).encode("ascii")


def read_models(payload):
    header, *body = payload.splitlines()
    p, cnf, variables, count = header.split()
    assert (p, cnf) == (b"p", b"cnf") and len(body) == int(count)
    clauses = []
    for line in body:
        a, b, c, end = map(int, line.split())
        assert end == 0 and len({abs(a), abs(b), abs(c)}) == 3
        clauses.append((a, b, c))
    assert {abs(lit) for row in clauses for lit in row} == set(range(1, int(variables) + 1))
    return {frozenset(lit for lit in model if lit > 0)
            for model in pycosat.itersolve(clauses, vars=int(variables))}


def source_models(source):
    result = set()
    for values in product((False, True), repeat=3):
        positive = frozenset(name for name, value in zip(SOURCE, values) if value)
        if all(any((abs(lit) in positive) == (lit > 0) for lit in row) for row in source):
            result.add(positive)
    return result


def audit(paired):
    rows = signed_rows(SOURCE)
    files = models = switched_models = 0
    for mask in range(1, 1 << len(rows)):
        source = [row for index, row in enumerate(rows) if mask & (1 << index)]
        physical = {q: encode(source, paired, q) for q in (2, 3, 6)}
        center, edited = physical[2], physical[3]
        assert len(center) == len(edited)
        assert sum((a ^ b).bit_count() for a, b in zip(center, edited)) == 1
        answers = {q: read_models(file) for q, file in physical.items()}
        assert answers[2] == {PUBLIC_MODEL}
        expected = source_models(source)
        assert {model.intersection(SOURCE) for model in answers[3]} == expected
        assert len(answers[3]) == len(expected)
        assert answers[2].isdisjoint(answers[3]) and answers[6] == answers[2] | answers[3]
        if paired:
            distance = len(SOURCE) + len(source) + 2
            assert all(len(model ^ PUBLIC_MODEL) == distance for model in answers[3])
        files += len(answers)
        models += sum(map(len, answers.values()))
        switched_models += len(answers[3])
    assert (files, models, switched_models) == (765, 2542, 1016)
    label = "paired" if paired else "unpaired"
    print(f"{label}: {files} files, {models} models, {switched_models} switched models")


if __name__ == "__main__":
    audit(paired=False)
    audit(paired=True)
