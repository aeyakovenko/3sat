"""Compare persistent assignment paths with brute-force physical CNF prefixes."""

import itertools
import random


class Ancestors:
    """The finite reference uses binary lifting for ancestor-at-depth queries."""

    def __init__(self):
        self.depth = [0]
        self.bit = [0]
        self.jump = [[]]

    def add_leaf(self, parent, bit):
        depth = self.depth[parent] + 1
        jump = [parent]
        while 1 << len(jump) <= depth:
            at = jump[-1]
            jump.append(self.jump[at][len(jump) - 1])
        node = len(self.bit)
        self.depth.append(depth)
        self.bit.append(bit)
        self.jump.append(jump)
        return node

    def read_bit(self, node, depth):
        delta = self.depth[node] - depth
        assert 0 <= delta < self.depth[node]
        while delta:
            step = delta.bit_length() - 1
            node = self.jump[node][step]
            delta -= 1 << step
        return self.bit[node]

    def full_path(self, node):
        result = []
        while node:
            result.append(self.bit[node])
            node = self.jump[node][0]
        return tuple(reversed(result))


def truth_table(clauses, variables):
    positions = {name: i for i, name in enumerate(variables)}
    return {
        bits for bits in itertools.product((0, 1), repeat=len(variables))
        if all(any(bits[positions[abs(lit)]] == (lit > 0) for lit in c)
               for c in clauses)
    }


def audit_formula(clauses, brute=True):
    tree = Ancestors()
    live = [0]
    key_seen = set()
    unique = []
    ids = {}
    counts = [1]
    attempts = old_nodes = 0
    for clause in clauses:
        key = tuple(sorted(clause))
        if key in key_seen:
            continue
        key_seen.add(key)
        unique.append(clause)
        old_size = len(ids)
        for lit in clause:
            if abs(lit) not in ids:
                ids[abs(lit)] = len(ids) + 1
        add_count = len(ids) - old_size
        old_nodes += len(live)
        next_live = []
        for node in live:
            assert tree.depth[node] == old_size
            already = any(tree.read_bit(node, ids[abs(lit)]) == (lit > 0)
                          for lit in clause if ids[abs(lit)] <= old_size)
            for bits in itertools.product((0, 1), repeat=add_count):
                attempts += 1
                if not already and not any(
                    bits[ids[abs(lit)] - old_size - 1] == (lit > 0)
                    for lit in clause if ids[abs(lit)] > old_size
                ):
                    continue
                end = node
                for bit in bits:
                    end = tree.add_leaf(end, bit)
                next_live.append(end)
        live = next_live
        counts.append(len(live))
        if brute:
            expected = truth_table(unique, ids)
            paths = {tree.full_path(x) for x in live}
            assert paths == expected and len(paths) == len(live)
    assert old_nodes == sum(counts[:-1])
    assert old_nodes <= attempts <= 8 * old_nodes
    assert len(tree.bit) - 1 <= attempts * 3
    return counts, old_nodes


def signed_clauses(variables):
    return [tuple(x*s for x, s in zip(names, signs))
            for names in itertools.combinations(range(1, variables + 1), 3)
            for signs in itertools.product((-1, 1), repeat=3)]


def check_families():
    formulas = visits = 0
    for variables, length in [(3, 4), (4, 2)]:
        for family in itertools.product(signed_clauses(variables), repeat=length):
            counts, _ = audit_formula(family)
            assert len(counts) == len(set(family)) + 1
            formulas += 1
            visits += len(counts) - 1
    rng = random.Random(20261126)
    alphabet = signed_clauses(6)
    for _ in range(150):
        family = rng.choices(alphabet, k=12)
        base, _ = audit_formula(family)
        repeated = [variant for c in family for variant in (c, tuple(reversed(c)), c)]
        variant, _ = audit_formula(repeated)
        assert variant == base
        formulas += 1
        visits += len(base) - 1
    sparse_names = (10**125 + 9, 10**37 + 3, 10**250 + 7)
    assert audit_formula([sparse_names, sparse_names[::-1]])[0] == [1, 7]
    return formulas, visits


def check_chain(size):
    anchors = signed_clauses(3)
    anchors.remove((1, 2, 3))  # All-false anchor assignment remains.
    clauses = anchors.copy()
    for x in range(5, 4 + size):
        clauses += [(x, 1, -(x - 1)), (-x, x - 1, 1)]
    counts, _ = audit_formula(clauses, brute=False)
    assert max(counts) <= 7 and counts[-1] == 2
    # Both paths are present up to the last pin, then one, then zero.
    yes = clauses + [(size + 3, 1, 2)]
    counts, _ = audit_formula(yes + [(-(size + 3), 1, 2)], brute=False)
    assert counts[-2:] == [1, 0]
    return len(clauses)


if __name__ == '__main__':
    formulas, visits = check_families()
    length = check_chain(1000)
    print(f'{formulas} families, {visits} distinct-clause prefix truth tables')
    print(f'{length} equality-chain clauses, 1000 ambiguous variables, at most 7 prefix models')
