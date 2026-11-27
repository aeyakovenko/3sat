"""Exact finite checks of a three-answer PCP compilation on binary decision trees."""

from itertools import product


def truth_table(arity, predicate):
    return sum(1 << row for row in range(1 << arity)
               if predicate(*[(row >> j) & 1 for j in range(arity)]))


SPLIT = truth_table(3, lambda parent, left, right: parent == left + right)
EDGES = [truth_table(2, lambda child, answer: not child or answer == bit) for bit in (0, 1)]
PIN_ZERO, PIN_ONE, IGNORE = 1, 2, 3


def slots(addresses, verdicts):
    """Positive variable IDs are private selector nodes; negative IDs address the shared proof."""
    leaves = len(addresses) + 1
    tests = [((1,), PIN_ONE)]
    for parent, address in enumerate(addresses, 1):
        tests.append(((parent, 2*parent, 2*parent+1), SPLIT))
        for b in (0, 1):
            tests.append(((2*parent+b, ~address), EDGES[b]))
    for index in range(leaves):
        tests.append(((leaves+index,), IGNORE if verdicts & (1 << index) else PIN_ZERO))
    tests.extend([((1,), IGNORE)] * 2)
    assert len(tests) == 4*leaves
    assert all(len(ids) == len(set(ids)) and table.bit_count() <= 3 for ids, table in tests)
    return tests


def cost(tests, selectors, proof):
    misses = 0
    for ids, table in tests:
        row = 0
        for j, var in enumerate(ids):
            bit = selectors >> (var-1) if var > 0 else proof >> ~var
            row |= (bit & 1) << j
        misses += (table >> row) & 1 == 0
    return misses


def binary_hull(arity, table):
    accepting = [row for row in range(1 << arity) if table >> row & 1]
    masks = [mask for mask in range(1 << arity) if mask.bit_count() <= 2]
    return sum(1 << row for row in range(1 << arity)
               if all(any((row ^ other) & mask == 0 for other in accepting)
                      for mask in masks))


def path_and_leaf(directions):
    leaves = len(directions)+1
    node = 1
    path = 1
    while node < leaves:
        node = 2*node + directions[node-1]
        path |= 1 << (node-1)
    return path, node-leaves


def subtree_minimum(directions, verdicts):
    """Compute exact minimum violated slots by eliminating selector bits bottom-up."""
    leaves = len(directions)+1
    costs = [None]*leaves + [(0, 1-((verdicts >> i) & 1)) for i in range(leaves)]
    for node in reversed(range(1, leaves)):
        route = directions[node-1]
        left_cost, right_cost = costs[2*node:2*node+2]
        costs[node] = tuple(min((p != l+r) + (l if route else r) + left_cost[l] + right_cost[r]
                                for l, r in product((0, 1), repeat=2)) for p in (0, 1))
    return min(1+costs[1][0], costs[1][1])


def audit_trees():
    cases = brute = 0
    for q in range(4):
        leaves = 1 << q
        for directions in product((0, 1), repeat=leaves-1):
            # The proof (0,1) realizes every possible adaptive local direction profile
            # by querying address 0 or 1 at each internal node, with arbitrary reuse.
            path, leaf = path_and_leaf(directions)
            for verdicts in range(1 << leaves):
                expected = 1-((verdicts >> leaf) & 1)
                assert subtree_minimum(directions, verdicts) == expected
                if q <= 2:
                    tests = slots(directions, verdicts)
                    assert cost(tests, path, 2) == expected
                    if q >= 1:
                        hulls = [(ids, binary_hull(len(ids), table)) for ids, table in tests]
                        assert binary_hull(3, SPLIT) == SPLIT | (1 << 1)
                        assert cost(hulls, 1, 2) == 0
                        honest_or_aborted = 1 if expected else path
                        assert cost(hulls, honest_or_aborted, 2) == 0
                        assert cost(tests, honest_or_aborted, 2) == expected
                    costs = [cost(tests, selectors, 2) for selectors in range(1 << (2*leaves-1))]
                    assert min(costs) == expected
                    assert costs.count(0) == 1-expected
                    brute += 1
                cases += 1
    print(f"{cases} tree profiles and leaf predicates through depth 3; "
          f"{brute} exhaustive comparisons with emitted slot truth tables through depth 2")


def audit_shared_bits():
    # Two seeds may sample the very same original address; only their selector trees are private.
    cases = 0
    for address0, address1 in product(range(2), repeat=2):
        for verdict0, verdict1 in product(range(4), repeat=2):
            pairs = [(address0, verdict0), (address1, verdict1)]
            tests = [slots((address,), verdicts) for address, verdicts in pairs]
            old = new = None
            for proof in range(4):
                misses = sum((verdicts >> ((proof >> address) & 1)) & 1 == 0
                             for address, verdicts in pairs)
                costs = [[cost(instance, selectors, proof) for selectors in range(8)]
                         for instance in tests]
                joint = min(a+b for a, b in product(*costs))
                assert joint == misses
                old = misses if old is None else min(old, misses)
                new = joint if new is None else min(new, joint)
            assert new == old
            cases += 1
    print(f"{cases} two-seed systems, each with exact optimum violation-count preservation")


def audit_exact_one():
    """Pin and implication costs after existentially choosing private auxiliary bits."""
    def rejects(a, b, c):
        return a+b+c != 1

    for z in (0, 1):
        assert min(rejects(z, u, v) + rejects(z, 1-u, 1-v)
                   for u, v in product((0, 1), repeat=2)) == z
    for child, wrong in product((0, 1), repeat=2):
        assert min(rejects(child, wrong, u) for u in (0, 1)) == (child and wrong)
    for parent, left, right in product((0, 1), repeat=3):
        assert rejects(1-parent, left, right) == (parent != left+right)
    print("Signed exact-one variant: all pin, implication, and split costs verified")


if __name__ == "__main__":
    audit_trees()
    audit_shared_bits()
    audit_exact_one()
