"""Exhaustive successor observations, cyclic verdicts, and optimal query costs."""
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import permutations, product
from math import comb, factorial


def cycle_table(order):
    table = [0] * len(order)
    for tail, head in zip(order, order[1:] + order[:1]):
        table[tail] = head
    return tuple(table)


def sign(order):
    return sum(a > b for i, a in enumerate(order) for b in order[i + 1:]) % 2


def marked_blocks(order, marks, mask):
    n = len(order)
    cuts = [i for i, v in enumerate(order) if not (mask >> v) & 1]
    if not cuts:
        return [len(marks)]
    result = []
    for i, stop in enumerate(cuts):
        start = cuts[i - 1]
        length = (stop - start) % n or n
        count = sum(order[(start + step) % n] in marks for step in range(1, length + 1))
        if count:
            result.append(count)
    return result


def arc_lengths(order, marks):
    points = [i for i, v in enumerate(order) if v in marks]
    return [(points[(i + 1) % len(points)] - j) % len(order) for i, j in enumerate(points)]


def matching_cost(lengths):
    k = len(lengths)
    return min(sum(lengths[(start + 2 * j) % k] for j in range(k // 2))
               for start in range(k))


def exact_certificates(orders, tables, k):
    n = len(orders[0])
    marks = set(range(k))
    mark_orders = [tuple(v for v in order if v in marks) for order in orders]
    signs = list(map(sign, mark_orders))
    best_full = [n] * len(tables)
    best_sign = best_full.copy()
    observations = 0
    for mask in range(1 << n):
        queried = [v for v in range(n) if (mask >> v) & 1]
        groups = defaultdict(list)
        for i, table in enumerate(tables):
            groups[tuple(table[v] for v in queried)].append(i)
        for ids in groups.values():
            counts = Counter(mark_orders[i] for i in ids)
            blocks = marked_blocks(orders[ids[0]], marks, mask)
            assert len(counts) == factorial(len(blocks) - 1)
            assert len(set(counts.values())) == 1
            sign_counts = Counter(signs[i] for i in ids)
            determined = sum(size % 2 for size in blocks) == 1
            assert (len(sign_counts) == 1) == determined
            if not determined:
                assert sign_counts[0] == sign_counts[1]
            for i in ids:
                if len(counts) == 1:
                    best_full[i] = min(best_full[i], len(queried))
                if determined:
                    best_sign[i] = min(best_sign[i], len(queried))
            observations += 1
    for i, order in enumerate(orders):
        lengths = arc_lengths(order, marks)
        assert best_full[i] == n - sum(sorted(lengths)[-2:])
        assert best_sign[i] == matching_cost(lengths)
    assert max(best_sign) == n * (k // 2) // k
    return observations


def exact_strategies(tables, answers, parity, k):
    """Optimize all decision trees on actual completion sets for the given n."""
    n = len(tables[0])

    @cache
    def solve(ids, remaining):
        frequencies = Counter(answers[i] for i in ids)
        if len(frequencies) == 1:
            return Fraction(0), 0, (len(ids),) * (remaining + 1)
        best_mean = n
        best_worst = n
        correct = [max(frequencies.values())] * (remaining + 1)
        for v in range(n):
            split = defaultdict(list)
            for i in ids:
                split[tables[i][v]].append(i)
            if len(split) == 1:
                continue
            children = [(len(g), solve(tuple(g), remaining - 1)) for g in split.values()]
            mean = 1 + sum(size * child[0] for size, child in children) / len(ids)
            best_mean = min(best_mean, mean)
            best_worst = min(best_worst, 1 + max(child[1] for _, child in children))
            for budget in range(1, remaining + 1):
                correct[budget] = max(correct[budget],
                                      sum(child[2][budget - 1] for _, child in children))
        return best_mean, best_worst, tuple(correct)

    mean, worst, successes = solve(tuple(range(len(tables))), n)
    coefficient = Fraction(2, k)
    if parity:
        coefficient = Fraction(1)
        for j in range(3, k + 1, 2):
            coefficient *= Fraction(j - 1, j)
    assert mean == n * (1 - coefficient) and worst == n - 2
    if parity and k == 3:
        for q in range(n - 1):
            predicted = 1 - Fraction(comb(n - 1 - q, 2), 2 * comb(n - 1, 2))
            assert Fraction(successes[q], len(tables)) == predicted
    return solve.cache_info().currsize


def horn_check(table, marked_order):
    n = len(table)
    # The two public flags are already pinned. X_0 is true and X_1 is false.
    sat = any(bits[0] and not bits[1]
              and all(i == 2 or not bits[i] or bits[table[i]] for i in range(n))
              for bits in product((False, True), repeat=n))
    assert sat == (marked_order.index(2) < marked_order.index(1))


def main():
    fibers = states = formulas = 0
    for n in range(3, 8):
        orders = [(0,) + rest for rest in permutations(range(1, n))]
        tables = list(map(cycle_table, orders))
        for order, table in zip(orders, tables):
            horn_check(table, order)
            formulas += 1
        for k in range(3, n + 1, 2):
            fibers += exact_certificates(orders, tables, k)
            if n <= 6:
                marked = [tuple(v for v in order if v < k) for order in orders]
                states += exact_strategies(tables, list(map(sign, marked)), True, k)
                states += exact_strategies(tables, marked, False, k)
    print(f"Checked {fibers:,} partial-table fibers, {states:,} decision-tree states, "
          f"and {formulas:,} explicit Horn verdicts.")


if __name__ == "__main__":
    main()
