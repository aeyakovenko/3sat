"""Compare exact elimination on shared timing circuits with a full interval census."""

from collections import Counter
from itertools import product
from math import comb, prod
from random import Random


def ranked(values, index):
    return sorted(values)[index]


def eliminate(factors, variables):
    """Explicitly sum each wire, including multiplications on variables shared by gates."""
    while variables:
        def combined_scope(variable):
            return set().union(*(scope for scope, _ in factors if variable in scope))

        variable = min(variables, key=lambda v: (len(combined_scope(v)), v))
        variables.remove(variable)
        group = [(scope, table) for scope, table in factors if variable in scope]
        other = [(scope, table) for scope, table in factors if variable not in scope]
        scope = sorted(combined_scope(variable))
        kept = tuple(v for v in scope if v != variable)
        group_indices = [(tuple(scope.index(v) for v in s), t) for s, t in group]
        keep_indices = tuple(scope.index(v) for v in kept)
        result = Counter()
        for row in product(range(4), repeat=len(scope)):
            weight = prod(t.get(tuple(row[i] for i in indices), 0)
                          for indices, t in group_indices)
            if weight:
                result[tuple(row[i] for i in keep_indices)] += weight
        factors = other + [(kept, result)]
    return prod(table.get((), 0) for _, table in factors)


def forced_count(workers, gates, left, right):
    factors = []
    for variable, choices in enumerate(workers):
        distribution = Counter((2 * (lo >= left) + (hi <= right),) for lo, hi in choices)
        factors.append(((variable,), distribution))
    for out, (args, rank) in enumerate(gates, start=len(workers)):
        distinct = tuple(sorted(set(args)))
        indices = tuple(distinct.index(v) for v in args)
        transition = {}
        for states in product(range(4), repeat=len(distinct)):
            lower = sum(bool(states[i] & 2) for i in indices) >= len(args) - rank
            upper = sum(bool(states[i] & 1) for i in indices) >= rank + 1
            transition[(*states, 2 * lower + upper)] = 1
        factors.append(((*distinct, out), transition))
    root = len(workers) + len(gates) - 1
    factors.append(((root,), {(3,): 1}))
    return eliminate(factors, set(range(root + 1)))


def census(workers, gates):
    result = Counter()
    for choices in product(*workers):
        intervals = list(choices)
        for args, rank in gates:
            l = ranked([intervals[i][0] for i in args], rank)
            r = ranked([intervals[i][1] for i in args], rank)
            intervals.append((l, r))
        result[intervals[-1]] += 1
    return result


def check():
    rng = Random(37229)
    windows = 0
    for example in range(48):
        workers = []
        for _ in range(3):
            choices = []
            for _ in range(3):
                a, b = sorted(rng.choices(range(4), k=2))
                choices.append((a, a if example % 2 == 0 else b))
            workers.append(choices)
        gates = []
        for idx in range(4):
            arity = rng.randint(2, 3)
            args = rng.choices(range(len(workers) + idx), k=arity)
            gates.append((args, rng.randrange(arity)))
        distribution = census(workers, gates)
        for l in range(4):
            for r in range(l, 4):
                expected = sum(c for (a, b), c in distribution.items() if l <= a and b <= r)
                assert expected == forced_count(workers, gates, l, r)
                windows += 1
    # Median of 101 reports. Three quarters of each worker's mass is an exact
    # vote for the same word, with one quarter giving no local information.
    k = 101
    forced = sum(comb(k, m) * 3**m for m in range(k // 2 + 1, k + 1))
    assert forced * 1000 > 999 * 4**k and 3**k * 10**12 < 4**k
    return windows


if __name__ == '__main__':
    print(f'{check()} interval windows agree with exhaustive enumeration; quorum bounds passed')
