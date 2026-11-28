"""Ordinary ASCII 3-CNF search and common-schedule audit. Each event is a DFS node or one incidence update."""
from itertools import combinations, product


def block_length(groups, j, length):
    return (length + groups - 1) // groups + (length + (1 << j) - 1) // (1 << j)


def formula(groups, block, length, negative):
    unit, pad, other_pad = (odd << block for odd in (1, 3, 5))
    data = [(2 * t + 1) << j for j in range(groups) if j != block
            for t in range(1, block_length(groups, j, length) + 1)]
    rows = [(unit, s * pad, t * other_pad) for s, t in product((-1, 1), repeat=2)]
    if negative:
        rows += [(-unit, s * pad, t * other_pad) for s, t in product((-1, 1), repeat=2)]
    rows += [(-unit, x, s * pad) for x in data for s in (-1, 1)]
    header = f'p cnf {max(abs(x) for row in rows for x in row)} {len(rows)}\n'
    return (header + ''.join(' '.join(map(str, row)) + ' 0\n' for row in rows)).encode('ascii')


def parse(data):
    lines = data.splitlines()
    prefix, typ, max_name, count = lines[0].split()
    assert (prefix, typ) == (b'p', b'cnf') and int(count) == len(lines) - 1
    incidence = {}
    for k, line in enumerate(lines[1:]):
        *literals, zero = map(int, line.split())
        assert zero == 0 and len(literals) == len({abs(x) for x in literals}) == 3
        for lit in literals:
            assert 0 < abs(lit) <= int(max_name)
            incidence.setdefault(abs(lit), []).append((k, lit > 0))
    return incidence, int(count)


def valuation(name):
    return (name & -name).bit_length() - 1


def events(incidence, clause_count, chosen):
    names = [name for name in incidence if valuation(name) == chosen]
    names += [name for name in incidence if valuation(name) != chosen]
    free = [3] * clause_count
    sat = [0] * clause_count
    contradicted = resolved = 0

    def assign(name, bit, direction):
        nonlocal contradicted, resolved
        for row, positive in incidence[name]:
            contradicted -= (free[row] == 0 and sat[row] == 0)
            resolved -= sat[row] > 0
            free[row] -= direction
            sat[row] += direction * (positive == bit)
            contradicted += (free[row] == 0 and sat[row] == 0)
            resolved += sat[row] > 0
            yield ('occurrence', name, bit, row, direction)

    def dfs(depth):
        yield ('node', depth, contradicted, resolved)
        if contradicted:
            return False
        if resolved == clause_count:
            return True
        assert depth < len(names)
        for bit in (False, True):
            yield from assign(names[depth], bit, 1)
            if (yield from dfs(depth + 1)):
                return True
            yield from assign(names[depth], bit, -1)
        return False

    return (yield from dfs(0))


def run(incidence, count, chosen):
    work = nodes = 0
    cursor = events(incidence, count, chosen)
    while True:
        try:
            event = next(cursor)
        except StopIteration as result:
            return result.value, work, nodes
        work += 1
        nodes += event[0] == 'node'


def controller(incidence, count, active, selector):
    cursors = [events(incidence, count, j) for j in range(active)]
    finished = [None] * active
    while True:
        observations = []
        for j, cursor in enumerate(cursors):
            if finished[j] is None:
                try:
                    observations.append(next(cursor))
                except StopIteration as result:
                    finished[j] = result.value
                    observations.append(('halt', result.value))
            else:
                observations.append(('idle',))
        yield tuple(observations), tuple(finished)
        offers = [(j + 1, verdict) for j, verdict in enumerate(finished) if verdict is not None]
        if offers:
            offers.append((0, offers[0][1]))
        for tag, verdict in offers:
            if selector == tag:
                return verdict
        if all(value is not None for value in finished):
            return finished[0]


def test():
    for width in range(2, 12):
        modulus = 1 << width
        for increments in range(1, 80):
            selector = -increments % modulus
            for _ in range(increments):
                selector = (selector + 1) % modulus
            assert selector == 0
    files = pairs = 0
    for groups, length in ((2, 1), (2, 3), (2, 4), (3, 2), (3, 3), (4, 2)):
        for block, negative in product(range(groups), (False, True)):
            data = formula(groups, block, length, negative)
            incidence, count = parse(data)
            guests = [run(incidence, count, j) for j in range(groups)]
            for j, (verdict, steps, nodes) in enumerate(guests):
                assert verdict == (not negative)
                if j == block:
                    assert steps <= 200 * (groups * length + 1)
                else:
                    assert nodes >= 2 ** block_length(groups, j, length)
            # Check all pairs of actual shared event streams through the earlier retirement.
            # A spare or out-of-range selector ends when all guests have stopped.
            selectors = (0, *range(1, groups + 1), groups + 2)
            for a, b in combinations(selectors, 2):
                cursors = [controller(incidence, count, groups, s) for s in (a, b)]
                rounds = []
                for s in (a, b):
                    if s == 0: rounds.append(min(v[1] for v in guests) + 1)
                    elif s > groups: rounds.append(max(v[1] for v in guests) + 1)
                    else: rounds.append(guests[s - 1][1] + 1)
                for _ in range(min(rounds)):
                    assert next(cursors[0]) == next(cursors[1])
                for c, r in zip(cursors, rounds):
                    if r == min(rounds):
                        try: next(c)
                        except StopIteration as result: assert result.value == (not negative)
                        else: raise AssertionError('failed to retire')
                pairs += 1
            if groups == 2 and length == 4 and block == 1:
                print(f'{len(data)*8} bits, {"NO" if negative else "YES"}, guest (events, nodes)',
                      [g[1:] for g in guests])
            files += 1
    print(f'{files} proper files, {pairs} paired event streams, including the first-completion control')


if __name__ == '__main__':
    test()
