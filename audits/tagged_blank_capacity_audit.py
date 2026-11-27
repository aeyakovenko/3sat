"""Exhaust small affine subspaces in tagged arrays; check the general integer bounds."""

from itertools import combinations_with_replacement, permutations


def injective_rank(q, demand, count):
    return sum(min(count, demand * (q >> j)) for j in range(1, q.bit_length()))


def tagged_rank(q, demand, count):
    budget = q * demand
    if q == 1:
        return min(count, budget)
    if 2 * count <= budget:
        return injective_rank(q, demand, count)
    return min(budget, budget - 2*demand + 2*count//q)


def packed(row, width):
    return sum(value << (slot*width) for slot, value in enumerate(row))


def exhaustive_rank(q, demand, count):
    width = q.bit_length()
    anchors = [row for row in combinations_with_replacement(range(q+1), count)
               if all(row.count(value) <= demand for value in range(q))]
    allowed = {packed(arrangement, width) for row in anchors for arrangement in set(permutations(row))}
    best = 0

    def extend(candidates, pivot, dimension):
        # All vectors retained here have zero in the previous pivot columns.
        # Each still takes the entire previously chosen flat into the valid set.
        nonlocal best
        best = max(best, dimension)
        if (1 << (best-dimension+1)) > len(candidates):
            return
        for vector in candidates:
            high = vector.bit_length()
            if high <= pivot:
                continue
            bit = 1 << (high-1)
            next_candidates = {v for v in candidates if not v & bit and v ^ vector in candidates}
            extend(next_candidates, high, dimension+1)

    for row in anchors:
        anchor = packed(row, width)
        extend({anchor ^ x for x in allowed}, 0, 0)
    return best


def check_bounds():
    budgets = 0
    for w in range(1, 8):
        q = 1 << w
        for demand in range(1, 6):
            budget = q*demand
            for count in range(budget+q+1):
                best = tagged_rank(q, demand, count)
                for optional in range(min(count, budget)+1):
                    ordinary = count-optional
                    bound = optional + sum(min(ordinary, (budget-optional) >> j) for j in range(1,w+1))
                    assert bound <= best
                if 2*count <= budget:
                    small, larger = divmod(count, demand)
                    ranks = (demand-larger)*injective_rank(q, 1, small) + larger*injective_rank(q, 1, small+1)
                    assert ranks == best
                else:
                    optional_groups = min(demand, 2*count//q-demand)
                    assert optional_groups*q + (demand-optional_groups)*(q//2) <= count
                    assert optional_groups*q + (demand-optional_groups)*(q-1) == best
                budgets += 1
    return budgets


if __name__ == '__main__':
    settings = [(1, 2, 4), (2, 1, 4), (2, 2, 5), (4, 1, 4), (4, 2, 3)]
    for q, demand, maximum in settings:
        values = [exhaustive_rank(q, demand, count) for count in range(maximum+1)]
        assert values == [tagged_rank(q, demand, count) for count in range(maximum+1)]
        print(f'Q={q}, D={demand}, m=0..{maximum}: {values}')
    print(f'{check_bounds()} arithmetic envelopes and matching layer allocations')
