"""Finite checks for chronological certificates on uninterrupted two-winner blocks."""

from functools import cache
from itertools import product


@cache
def expert_menu(start_pool, history):
    """Recover the two public pairs from *rank* history, sharing the least live second."""
    live = set(range(start_pool))
    previous_second = None
    for first, second in history:
        assert first != second and {first, second} <= live
        live.remove(first)
        previous_second = min(live)  # Least live at the intervening response date.
        live.remove(second)
    second = min(live)
    firsts = sorted(live - {second, previous_second})[:2]
    assert len(firsts) == 2
    return tuple((first, second) for first in firsts)


def finite_tree(depth):
    """Index the full binary tree by integers, but store ordinary ordered rank pairs."""
    pool = 2 * depth + 2
    histories = {1: ()}
    mistakes = {1: (0, 0)}
    for node in range(1, 1 << depth):
        history = histories[node]
        pairs = expert_menu(pool, history)
        assert pairs[0] < pairs[1] and pairs[0][1] == pairs[1][1]
        for expert, pair in enumerate(pairs):
            child = 2 * node + expert
            histories[child] = history + (pair,)
            mistakes[child] = tuple(count + (claimed == pair)
                                    for count, claimed in zip(mistakes[node], pairs))
    for node in range(1 << depth, 2 << depth):
        assert mistakes[node] == score_every_date(pool, histories[node])
    return histories, mistakes


def score_every_date(pool, history):
    """Score also the response dates and the terminal tag against the physical run."""
    winners = tuple(rank for pair in history for rank in pair) + (pool,)
    live = set(range(pool))
    previous_second = None
    losses = [0, 0]
    for date, winner in enumerate(winners):
        second = min(live)
        if len(live) >= 4:
            firsts = sorted(live - {second, previous_second})[:2]
            for expert, first in enumerate(firsts):
                losses[expert] += winners[date:date + 2] == (first, second)
        previous_second = second
        live.discard(winner)
    return tuple(losses)


def walk(depth, row_witnesses):
    """Feasibility uses one timely witness per row; the real search also checks priority."""
    end = 1 << depth
    reachable = [1]
    full = []
    while reachable:
        node = reachable.pop()
        if node >= end:
            full.append(node)
            continue
        for bit, witnesses in enumerate(row_witnesses(node)):
            if witnesses:
                reachable.append(2 * node + bit)
    actual = 1
    while actual < end:
        rows = row_witnesses(actual)
        accepted = next((index for index, witnesses in enumerate(rows) if witnesses), None)
        if accepted is None:
            break
        actual = 2 * actual + accepted
    return actual, full


def check_adaptive_trees():
    depth = 3
    end = 1 << depth
    histories, mistakes = finite_tree(depth)
    cases = guarded = unanimous = greedy_dead_ends = 0
    for masks in product(range(4), repeat=end - 1):
        def rows(node):
            mask = masks[node - 1]
            return (bool(mask & 1), bool(mask & 2))

        actual, full = walk(depth, rows)
        cases += 1
        if all(masks):
            guarded += 1
            assert actual >= end and full
        if actual < end:
            greedy_dead_ends += bool(full)
            continue
        assert histories[actual] == min(histories[node] for node in full)
        # Ties choose expert zero. An existential full path with the indicated
        # inequality is the threshold certificate for the corresponding bit.
        can_choose_zero = any(mistakes[node][0] <= mistakes[node][1] for node in full)
        can_choose_one = any(mistakes[node][0] > mistakes[node][1] for node in full)
        bits = {int(mistakes[node][0] > mistakes[node][1]) for node in full}
        if len(bits) == 1:
            unanimous += 1
            actual_bit = int(mistakes[actual][0] > mistakes[actual][1])
            assert (can_choose_zero, can_choose_one) == (actual_bit == 0, actual_bit == 1)
        else:
            assert can_choose_zero and can_choose_one
    assert guarded == 3 ** (end - 1) and greedy_dead_ends > 0
    return cases, guarded, unanimous, greedy_dead_ends


def check_guard_lengths():
    cases = 0
    for pool in range(4, 70):
        for live_guard in range(4, pool + 1):
            length = (pool - live_guard) // 2 + 1
            remaining = pool
            for _ in range(length):
                assert remaining >= live_guard
                remaining -= 2
            assert remaining < live_guard
            cases += 1
    return cases


def assignment_satisfies(assignment, formula):
    return all(any(bool(assignment & (1 << (abs(lit) - 1))) == (lit > 0)
                   for lit in clause) for clause in formula)


def check_formula_forks():
    # These eight genuine three-literal clauses block the eight different rows.
    blocks = tuple(tuple(sign * (var + 1) for var, sign in enumerate(signs))
                   for signs in product((1, -1), repeat=3))
    units = ((1, 1, 1), (-1, -1, -1), (2, 2, 2), (-2, -2, -2))
    checked = satisfiable = unsatisfiable = 0
    for depth in range(1, 6):
        histories, mistakes = finite_tree(depth)
        for clauses in (blocks, units):
            for mask in range(1 << len(clauses)):
                formula = tuple(c for i, c in enumerate(clauses) if mask & (1 << i))
                assert all(len(c) == 3 for c in formula)
                witnesses = tuple(a for a in range(8) if assignment_satisfies(a, formula))
                if clauses == blocks:
                    assert len(witnesses) == 8 - len(formula)
                else:
                    assert bool(witnesses) == (mask & 3 != 3 and mask & 12 != 12)

                def rows(node):
                    if node == 1:
                        return witnesses, (0,)  # The fallback is feasible even on YES.
                    winner_pair = histories[node][0]
                    first_expert = expert_menu(2 * depth + 2, ()).index(winner_pair)
                    return tuple((0,) if e == first_expert else () for e in (0, 1))

                actual, feasible = walk(depth, rows)
                assert histories[actual] == min(histories[node] for node in feasible)
                assert mistakes[actual] == ((depth, 0) if witnesses else (0, depth))
                # A fallback certificate for the opposite preference persists
                # on YES. It witnesses a feasible transcript, not the actual one.
                assert {mistakes[node] for node in feasible} == (
                    {(depth, 0), (0, depth)} if witnesses else {(0, depth)}
                )
                checked += 1
                satisfiable += bool(witnesses)
                unsatisfiable += not witnesses
    return checked, satisfiable, unsatisfiable


if __name__ == '__main__':
    print('Adaptive trees (all, full-guarded, full and unanimous, greedy dead end'
          ' with a feasible full alternative):', check_adaptive_trees())
    print('Guard and pool size combinations:', check_guard_lengths())
    print('Ordinary 3-CNF forks (total, SAT, UNSAT):', check_formula_forks())
