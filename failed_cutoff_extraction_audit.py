"""Exhaust finite extraction games and check actual one-hot queries on a nested SAT chain."""

from functools import cache
from itertools import combinations, islice, product
from math import ceil, log2

import pycosat

from one_byte_dense_successor_audit import encode, parse
from ordered_cutoff_pruning_audit import physical_host


def masks(values):
    return sum(1 << value for value in values)


def greedy_cover(family, m):
    remaining = (1 << m) - 1
    blocks = []
    while remaining:
        point = remaining & -remaining
        chosen = max((interval for interval in family if interval & point), key=int.bit_length)
        blocks.append((point, chosen & remaining))
        remaining &= ~chosen
    assert all(sum(bool(interval & point) for point, _ in blocks) <= 1 for interval in family)
    return blocks


def check_game(m, family):
    plant = 1 << (m - 1)
    worlds = list(range(plant, 2 * plant))
    all_worlds = (1 << len(worlds)) - 1
    answers = [masks(i for i, w in enumerate(worlds) if (w & -w) & interval)
               for interval in family]

    def query_partition(group):
        return masks(i for i, w in enumerate(worlds) if group & w)

    full_queries = [query_partition(group) for group in range(1, plant)]
    point_queries = [query_partition(1 << j) for j in range(m - 1)]

    def one_pair(live):
        return any(live & options == live for options in answers)

    def depth(queries):
        @cache
        def solve(live):
            if one_pair(live):
                return 0
            return 1 + min(max(solve(live & test), solve(live & ~test)) for test in queries
                           if live & test and live & ~test)
        return solve(all_worlds)

    def works(batch):
        groups = {all_worlds}
        for test in batch:
            groups = {part for group in groups for part in (group & test, group & ~test) if part}
        return all(one_pair(group) for group in groups)

    parallel = next(q for q in range(m) if any(works(batch) for batch in combinations(full_queries, q)))
    k = len(greedy_cover(family, m))
    assert depth(full_queries) == ceil(log2(k)) and parallel == k - 1
    assert depth(point_queries) == min(m - interval.bit_count() for interval in family if interval & plant)
    return k


def interval_catalog():
    games = {}
    for m in range(1, 5):
        intervals = [masks(range(i, j + 1)) for i in range(m) for j in range(i, m)]
        for encoded in range(1, 1 << len(intervals)):
            family = [x for j, x in enumerate(intervals) if encoded & (1 << j)]
            covered = 0
            for x in family:
                covered |= x
            if covered == (1 << m) - 1:
                k = check_game(m, family)
                games[m, k] = games.get((m, k), 0) + 1
    assert max(k for _, k in games) == 4
    return sum(games.values())


def suffix_source(v, pin):
    source = []
    for lower in range(1, v):
        upper = lower + 1
        pad = next(j for j in range(1, v + 1) if j not in (lower, upper))
        source.extend((lower, -upper, sign * pad) for sign in (-1, 1))
    a, b = islice((j for j in range(1, v + 1) if j != pin), 2)
    source.extend((pin, x * a, y * b) for x, y in product((-1, 1), repeat=2))
    return source


def signed_eval(clauses, assignment):
    return all(any(bool(assignment & (1 << (abs(x) - 1))) == (x > 0) for x in row) for row in clauses)


def physical_chain():
    checks = queries = 0
    for v in range(3, 9):
        for pin in range(1, v + 1):
            source = suffix_source(v, pin)
            actual = {a for a in range(1 << v) if signed_eval(source, a)}
            assert actual == {(1 << h) - 1 for h in range(pin, v + 1)}
            checks += 1 << v
            if v != 3:
                continue
            for depth in range(1, v + 1):
                cutoffs = [(1 << (v - depth)) - 1, (1 << (v - depth + 1)) - 1]
                _, switches, _, center = physical_host(source, v, cutoffs, 1)
                pos = []
                labels = []
                for (p, q, a, _), end in zip(switches, cutoffs):
                    marker = f'\n{p} {q} {a} 0'.encode()
                    assert center.count(marker) == 1
                    address = center.index(marker) + len(marker) - 3
                    raw = bytearray(center)
                    raw[address] ^= 1
                    rows = parse(bytes(raw))
                    assert encode(rows) == bytes(raw)
                    truth = min(actual) <= end
                    answer = pycosat.solve(list(rows))
                    if truth:
                        assert isinstance(answer, list)
                        model = set(answer)
                        assert all(-x not in model for x in model)
                        assert all(any(x in model for x in row) for row in rows)
                    else:
                        assert answer == 'UNSAT'
                    labels.append(truth)
                    pos.append(address)
                    queries += 1
                assert pos[0] != pos[1] and (labels[0] != labels[1]) == (v - depth + 1 == pin)
    return checks, queries


if __name__ == '__main__':
    games = interval_catalog()
    checks, files = physical_chain()
    print(f'{games} complete game families, all existential filters, all point tests through 4 candidates')
    print(f'{checks} direct source assignments; {files} actual degree-four files in nested dyadic examples')
