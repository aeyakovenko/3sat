"""Exact permutation-menu census for forcing a distinguished last discovery.

Zero denotes the query packet Q. Menus contain labeled permutations. Each
first address must have a possible nonzero answer with a winning residual
menu. No solver packages are required.
"""

from functools import cache
from itertools import combinations, permutations


@cache
def layouts(p):
    return tuple(permutations(range(p + 1)))


@cache
def fiber_tables(p):
    """For each (position, data label), embed the (p-1) permutation space."""
    number = {row: i for i, row in enumerate(layouts(p))}
    tables = []
    for i in range(p + 1):
        row = []
        for a in range(1, p + 1):
            large_bits = []
            for small in layouts(p - 1):
                adjusted = tuple(v + (v >= a) for v in small)
                large = adjusted[:i] + (a,) + adjusted[i:]
                large_bits.append(1 << number[large])
            row.append((sum(large_bits), large_bits))
        tables.append(row)
    return tables


def embed(small, large_bits):
    return sum(bit for j, bit in enumerate(large_bits) if small >> j & 1)


def project(large, large_bits):
    return sum(1 << j for j, bit in enumerate(large_bits) if large & bit)


@cache
def winning(p, menu):
    if not p:
        return bool(menu)
    # Every pair of positions forced to return the same label has disjoint
    # witnesses. Since p labels serve p+1 positions, the lower bound doubles.
    if menu.bit_count() < 1 << p:
        return False
    for choices in fiber_tables(p):
        for fiber, large_bits in choices:
            kept = menu & fiber
            if kept.bit_count() >= 1 << (p - 1) and winning(p - 1, project(kept, large_bits)):
                break
        else:
            return False
    return True


def direct_game(rows, positions):
    """Literal game recursion, independent of the size bound and bit masks."""
    if len(positions) <= 1:
        return bool(rows)
    for i in positions:
        remaining = tuple(j for j in positions if j != i)
        if not any(direct_game(tuple(row for row in rows if row[i] == a), remaining)
                   for a in {row[i] for row in rows} - {0}):
            return False
    return True


def minimum_success_mass(rows, positions):
    """Worst number of Q-last layouts, when all listed rows have unit weight."""
    if len(positions) == 1 or not rows:
        return len(rows)
    costs = []
    for i in positions:
        remaining = tuple(j for j in positions if j != i)
        costs.append(sum(minimum_success_mass(tuple(row for row in rows if row[i] == a), remaining)
                         for a in {row[i] for row in rows} - {0}))
    return min(costs)


def doubled(rows):
    """Append the new label in one branch, and exchange it with Q in the other."""
    a = len(rows[0])
    grown = []
    for row in rows:
        grown.append(row + (a,))
        grown.append(tuple(v if v else a for v in row) + (0,))
    return tuple(grown)


def least_unseen_layout(order):
    """Implement the increasing-cycle adversary on a fixed discovery order."""
    pending = [True] * len(order)
    output = [None] * len(order)
    least = 0
    for slot in order:
        pending[slot] = False
        if slot != least:
            output[slot] = slot
            continue
        while least < len(order) and not pending[least]:
            least += 1
        output[slot] = least if least < len(order) else 0
    assert output[order[-1]] == 0
    assert sorted(output) == list(range(len(order)))
    return tuple(output)


def minimum_candidates(p, previous):
    """All possible optimum menus, allowing two different first-reply witnesses.

    An optimum with 2**p rows is exactly the union of two disjoint optimum
    fibers sharing one reply label in different positions. Some unions fail
    the requirements at a third position; test the full game on every union.
    """
    tables = fiber_tables(p)
    found = set()
    examined = 0
    for a in range(p):
        lifted = [[embed(small, choices[a][1]) for small in previous] for choices in tables]
        for i, j in combinations(range(p + 1), 2):
            others = [choices for h, choices in enumerate(tables) if h not in (i, j)]
            for left in lifted[i]:
                for right in lifted[j]:
                    menu = left | right
                    examined += 1
                    if menu in found:
                        continue
                    # In the union the two construction sites already win.
                    if any(all((menu & mask).bit_count() < 1 << (p - 1) for mask, _ in choices)
                           for choices in others):
                        continue
                    if winning(p, menu):
                        found.add(menu)
    return examined, found


def main():
    previous = {1}
    doubled_example = ((0,),)
    for p in range(1, 5):
        doubled_example = doubled(doubled_example)
        slots = tuple(range(p + 1))
        assert len(set(doubled_example)) == 1 << p and direct_game(doubled_example, slots)
        examined, current = minimum_candidates(p, previous)
        numbers = {row: j for j, row in enumerate(layouts(p))}
        assert sum(1 << numbers[row] for row in doubled_example) in current
        if p <= 2:
            exact = set()
            for mask in range(1 << len(numbers)):
                rows = tuple(row for row, j in numbers.items() if mask >> j & 1)
                plays = direct_game(rows, slots)
                assert plays == winning(p, mask)
                if plays and len(rows) == 1 << p:
                    exact.add(mask)
            assert exact == current
        assert minimum_success_mass(layouts(p), slots) * len(slots) == len(layouts(p))
        if p <= 3:
            for menu in current:
                rows = tuple(row for row, j in numbers.items() if menu >> j & 1)
                assert minimum_success_mass(rows, slots) == 1
        print(f"p={p}: minimum {1 << p}, {len(current)} labeled minimizing menus; "
              f"{examined} ordered-by-position fiber unions tested", flush=True)
        previous = current

    doubled_example = ((0,),)
    for p in range(1, 8):
        doubled_example = doubled(doubled_example)
        layouts_seen = {least_unseen_layout(order) for order in permutations(range(p + 1))}
        assert layouts_seen == set(doubled_example)
    print("The least-unseen online adversary yields exactly its doubled menu "
          "on all discovery orders through p=7.")


if __name__ == "__main__":
    main()
