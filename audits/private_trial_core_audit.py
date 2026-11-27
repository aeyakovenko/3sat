"""Check CNF core composition and changes to short windows of priority trials."""

from itertools import product


def clause_mask(clause, assignments):
    return sum(1 << word for word in range(assignments)
               if any(bool(word & (1 << (abs(lit) - 1))) == (lit > 0) for lit in clause))


def restrictions(clauses, universe):
    """Least number of clauses yielding each satisfying-assignment set."""
    costs = {universe: 0}
    for clause in clauses:
        for before, cost in tuple(costs.items()):
            after = before & clause
            if after not in costs or cost + 1 < costs[after]:
                costs[after] = cost + 1
    return costs


def check_composition(truth, weights, bad_tables):
    cells = len(weights)
    next_var = cells + 1
    modules = []
    for i, weight in enumerate(weights):
        leaf = (i + 1) if truth & (1 << i) else -(i + 1)
        wire = list(range(next_var, next_var + weight - 1)) + [leaf]
        next_var += weight - 1
        modules.append([(wire[0],)] + [(-a, b) for a, b in zip(wire, wire[1:])])
    # The output is hardwired to the wrong pin. Each forbidden table produces
    # one ordinary width-at-most-three clause on the exported bits.
    scheduler = [tuple(-(i + 1) if table & (1 << i) else i + 1 for i in range(cells))
                 for table in range(1 << cells) if table not in bad_tables]
    assignments = 1 << (next_var - 1)
    universe = (1 << assignments) - 1
    inner = [[clause_mask(c, assignments) for c in block] for block in modules]
    outer = [clause_mask(c, assignments) for c in scheduler]
    exact = restrictions([c for block in inner for c in block] + outer, universe)[0]
    units = [clause_mask(((i + 1) if truth & (1 << i) else -(i + 1),), assignments)
             for i in range(cells)]
    # Measure the local forcing costs independently of the known chain lengths.
    for w, block, unit in zip(weights, inner, units):
        assert w == min(k for mask, k in restrictions(block, universe).items() if not mask & ~unit)
    outer_cost = restrictions(outer, universe)
    candidates = []
    for fixed in range(1 << cells):
        allowed, cost = universe, 0
        for i, unit in enumerate(units):
            if fixed & (1 << i):
                allowed &= unit
                cost += weights[i]
        cover = [size for mask, size in outer_cost.items() if not (mask & allowed)]
        if cover:
            candidates.append((cost, min(cover)))
    weighted = min(cost for cost, _ in candidates)
    assert exact == min(cost + outer_size for cost, outer_size in candidates)
    assert weighted <= exact <= weighted + len(scheduler)
    return exact > weighted


def composition_audit():
    count = strict = 0
    for rows in range(16):
        bad = {x for x in range(4) if rows & (1 << x)}
        for honest in sorted(set(range(4)) - bad):
            for weights in ((1, 1), (2, 3), (3, 1)):
                strict += check_composition(honest, weights, bad)
                count += 1
    bad_sets = ({1, 2, 4}, {1, 2, 4, 7}, {3, 5, 6, 7}, {6, 7}, {0}, set())
    for bad in bad_sets:
        for honest in sorted(set(range(8)) - bad):
            strict += check_composition(honest, (1, 2, 2), bad)
            count += 1
    return count, strict


def winner(word, active, retired):
    choices = word & active & ~retired
    return choices & -choices


def check_window(columns, active, before, rank):
    j = len(columns) - 1
    ebit = 1 << rank
    lower = ebit - 1
    if (rank > j or not ebit & active[j] or ebit & before[j]
            or winner(columns[j], active[j], before[j]) == ebit):
        return None
    t = next(s for s in range(j-rank, j+1) if s + (lower & ~before[s]).bit_count() == j)
    pending = [r for r in range(rank) if not before[t] & (1 << r)] + [rank]
    assert len(pending) == j-t+1
    retired = before[t]
    for s, r in enumerate(pending, start=t):
        assert s-r >= j-rank
        expected = 1 << r
        # Keep all genuine pulses and turn on only this stage's intended one.
        assert winner(columns[s] | expected, active[s], retired) == expected
        # Check the variant which sets all eligible entries to one as well.
        assert winner(active[s], active[s], retired) == expected
        retired |= expected
    return winner(columns[j] | ebit, active[j], before[j]) != ebit


def window_audit():
    count = needed_window = 0
    for ranks, stages in ((2, 4), (3, 3), (3, 4), (4, 3)):
        all_ranks = (1 << ranks) - 1
        gradual = [(1 << min(i + 1, ranks)) - 1 for i in range(stages)]
        for active in ([all_ranks] * stages, [all_ranks >> 1] + [all_ranks] * (stages-1), gradual):
            for columns in product(*(range(mask + 1) for mask in active)):
                before = [0]
                for col, mask in zip(columns[:-1], active[:-1]):
                    before.append(before[-1] | winner(col, mask, before[-1]))
                for r in range(ranks):
                    result = check_window(columns, active, before, r)
                    if result is not None:
                        count += 1
                        needed_window += result
    assert needed_window > 0
    return count, needed_window


if __name__ == '__main__':
    total, strict = composition_audit()
    histories, preempted = window_audit()
    print(f'{total} exact CNF core minima, {strict} with positive scheduler cost; '
          f'{histories} eligible losing windows, {preempted} preempted after a one-bit change')
