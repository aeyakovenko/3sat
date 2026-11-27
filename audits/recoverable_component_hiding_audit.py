"""Check the proper-3-CNF permutation sources and the exact small hiding bound."""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, permutations, product
from math import ceil
from random import Random


def make_formula(perm, pins=None):
    r = len(perm)
    left, right = list(range(1, r + 1)), list(range(r + 1, 2 * r + 1))
    hub, p, q = 2 * r + 1, 2 * r + 2, 2 * r + 3
    fresh = q + 1
    edges = list(zip(left, left[1:])) + list(zip(right, right[1:]))
    edges.extend((left[i], right[j]) for i, j in enumerate(perm))
    for path, count in ((left, 1), (right, 3)):
        for i, vertex in enumerate(path):
            for _ in range(count + (i == 0)):
                edges.append((vertex, fresh))
                fresh += 1
    clauses = [(hub, a, b) for a, b in edges]
    if pins is None:
        pinned = [hub, left[0]] + right[::2]
    else:
        i, subset = pins
        pinned = [hub, left[i]] + [right[j] for j in subset]
    for var in pinned:
        clauses.extend((-var, s * p, t * q) for s, t in product((1, -1), repeat=2))
    return clauses


def dimacs(clauses):
    v = max(abs(lit) for clause in clauses for lit in clause)
    return f"p cnf {v} {len(clauses)}\n" + "".join(
        " ".join(map(str, clause)) + " 0\n" for clause in clauses)


def extract(clauses):
    # All genuine cone triples have multiplicity one in the unsigned support.
    supports = Counter(tuple(sorted(map(abs, row))) for row in clauses)
    cone = [set(row) for row, count in supports.items() if count == 1]
    hub, = set.intersection(*cone)
    neighbors = defaultdict(set)
    for row in cone:
        a, b = row - {hub}
        neighbors[a].add(b)
        neighbors[b].add(a)

    def path(lower, upper):
        side = {v for v, n in neighbors.items() if lower <= len(n) <= upper}
        starts = [v for v in side if len(neighbors[v] & side) == 1]
        start = max(starts, key=lambda v: len(neighbors[v]))
        ordered, remaining = [start], side - {start}
        while remaining:
            nxt, = neighbors[ordered[-1]] & remaining
            ordered.append(nxt)
            remaining.remove(nxt)
        return ordered

    left, right = path(3, 4), path(5, 6)
    right_index = {v: i for i, v in enumerate(right)}
    answer = []
    for v in left:
        matched, = neighbors[v] & right_index.keys()
        answer.append(right_index[matched])
    return tuple(answer)


def satisfiable(clauses):
    if not clauses:
        return True
    if any(not row for row in clauses):
        return False
    units = [row[0] for row in clauses if len(row) == 1]
    literals = {lit for row in clauses for lit in row}
    pure = next((lit for lit in literals if -lit not in literals), None)
    if units:
        choice = units[:1]
    elif pure is not None:
        choice = [pure]
    else:
        choice = [clauses[0][0], -clauses[0][0]]
    for lit in choice:
        residual = [tuple(v for v in row if v != -lit) for row in clauses if lit not in row]
        if satisfiable(residual):
            return True
    return False


def renamed(clauses, rng):
    names = sorted({abs(lit) for row in clauses for lit in row})
    images = names.copy()
    rng.shuffle(images)
    mapping = {v: rng.choice((-1, 1)) * image for v, image in zip(names, images)}
    result = []
    for row in clauses:
        out = [mapping[abs(lit)] * (1 if lit > 0 else -1) for lit in row]
        rng.shuffle(out)
        result.append(tuple(out))
    rng.shuffle(result)
    return result


def check_sources():
    rng = Random(924)
    for r in (4, 6):
        lengths, positives, seen = set(), 0, set()
        for perm in permutations(range(r)):
            source = make_formula(perm)
            lengths.add(len(dimacs(source)))
            variant = renamed(source, rng)
            recovered = extract(variant)
            assert recovered == perm
            seen.add(recovered)
            actual = satisfiable(variant)
            assert actual == (perm[0] % 2 == 1)
            positives += actual
            if r == 4:
                for i, j in product(range(r), repeat=2):
                    assert satisfiable(make_formula(perm, (i, [j]))) == (perm[i] != j)
        assert len(lengths) == 1 and 2 * positives == len(seen)
        print(f"r={r}: {len(seen)} distinct types, {positives} SAT, {lengths.pop()} source bytes")


def check_buckets():
    # For each advice law the optimal minimum inclusion on b types is
    # min(1,t/b). Enumerate every advice assignment to check integer rounding.
    cases = 0
    for k in range(1, 8):
        for a in range(1, min(k, 3) + 1):
            for t in range(1, k + 1):
                best = max(min(Fraction(min(t, b), b) for b in Counter(labels).values())
                           for labels in product(range(a), repeat=k))
                assert best == min(1, Fraction(t, ceil(k / a)))
                # Check the conditional subset sampler, including padding-free b<t.
                b = ceil(k / a)
                samples = list(combinations(range(b), min(t, b)))
                event = [s for s in samples if 0 in s]
                tv = sum(abs(Fraction(s in event, len(event)) - Fraction(1, len(samples)))
                         for s in samples) / 2
                assert tv == 1 - best
                cases += 1
    print(f"{cases} finite minimax cases verified")


def check_lossy():
    r = 4
    rng = Random(144)
    perms = list(permutations(range(r)))
    masks = list(product(range(2), range(r), range(2)))
    questions = [(i, b, u, t) for i in range(r) for b, u, t in masks]

    def selected(j, b, u, t):
        return j % 2 == b and ((j & u).bit_count() + t) % 2 == 1

    truth = {}
    for perm in perms:
        answers = {}
        for i, b, u, t in questions:
            subset = [j for j in range(r) if selected(j, b, u, t)]
            actual = satisfiable(make_formula(perm, (i, subset)))
            assert actual == (perm[i] not in subset)
            answers[i, b, u, t] = 1 if actual else -1
        truth[perm] = answers

    predictors = [{q: rng.choice((-1, 1)) for q in questions} for _ in range(40)]
    for perm in perms:
        for stored in range(r + 1):
            predictor = {q: truth[perm][q] if q[0] < stored else 1 for q in questions}
            agreement = sum(v == truth[perm][q] for q, v in predictor.items())
            assert Fraction(agreement, len(questions)) == Fraction(3, 4) + Fraction(stored, 4 * r)
            predictors.append(predictor)
    for predictor in predictors:
        means, correlations = {}, {}
        for i, b in product(range(r), range(2)):
            values = [predictor[i, b, u, t] for u, t in product(range(r), range(2))]
            means[i, b] = Fraction(sum(values), len(values))
            for j in range(b, r, 2):
                terms = [predictor[i, b, u, t] * (-1 if selected(j, b, u, t) else 1)
                         for u, t in product(range(r), range(2))]
                correlations[i, j] = Fraction(sum(terms), len(terms))
            assert sum(correlations[i, j] ** 2 for j in range(b, r, 2)) <= 1
        for perm in perms:
            accuracy = Fraction(sum(predictor[q] == truth[perm][q] for q in questions), len(questions))
            row_sum = sum(means[i, 1 - j % 2] + correlations[i, j] for i, j in enumerate(perm))
            assert accuracy == Fraction(1, 2) + row_sum / (4 * r)
    print(f"{len(perms) * len(questions)} affine-mask DIMACS queries; "
          f"{len(predictors) * len(perms)} exact predictor/target score identities")


if __name__ == "__main__":
    check_sources()
    check_buckets()
    check_lossy()
