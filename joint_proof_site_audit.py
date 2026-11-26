"""Check joint lexicographic witnesses with real inner proper DIMACS files.

The outer existential verifier is executed by enumerating its candidate word.
Only variables of the source formula take part in the order. Auxiliary gates
used to compile an inner question are local to that question.
"""

from collections import Counter
from itertools import product

from compiled_horn_receipt_audit import Circuit, exact_sat


def words(n):
    return product((False, True), repeat=n)


def dimacs(n, clauses):
    lines = [f"p cnf {n} {len(clauses)}"]
    lines.extend(" ".join(map(str, (*row, 0))) for row in clauses)
    return ("\n".join(lines) + "\n").encode("ascii")


def source_copy(net, n, clauses):
    inputs = [net.fresh() for _ in range(n)]
    for clause in clauses:
        net.add(*(inputs[abs(lit) - 1] if lit > 0 else -inputs[-lit - 1] for lit in clause))
    return inputs


def inner_file(n, clauses, order, prefix=(), less_than=None):
    """Compile F(z) with assigned prefix and optional strict z < candidate."""
    net = Circuit(True)
    inputs = source_copy(net, n, clauses)
    for pos, value in zip(order, prefix):
        net.add(inputs[pos] if value else -inputs[pos])
    if less_than is not None:
        assert len(less_than) == len(order)
        smaller = -net.one
        for pos, bound in reversed(tuple(zip(order, less_than))):
            literal_zero = -inputs[pos]
            smaller = net.either(literal_zero, smaller) if bound else net.both(literal_zero, smaller)
        net.add(smaller)
    return net.bytes()


def pair_file(n, clauses, order, pinned, prefix_length):
    """Do two satisfying projected words obey the zero pins and differ early?"""
    net = Circuit(True)
    left = source_copy(net, n, clauses)
    right = source_copy(net, n, clauses)
    for i in pinned:
        net.add(-left[order[i]])
        net.add(-right[order[i]])
    differ = -net.one
    for pos in order[:prefix_length]:
        a, b = left[pos], right[pos]
        unequal = net.either(net.both(a, -b), net.both(-a, b))
        differ = net.either(differ, unequal)
    net.add(differ)
    return net.bytes()


def affine_dimension(projected):
    offsets = [sum(int(value != first) << i for i, (value, first) in enumerate(zip(w, projected[0])))
               for w in projected]
    pivots = {}
    for v in offsets:
        while v:
            p = v.bit_length() - 1
            if p not in pivots:
                pivots[p] = v
                break
            v ^= pivots[p]
    return len(pivots)


def recover_by_disagreements(n, clauses, order, projected, stats):
    pins = []
    survivors = projected
    start_dimension = affine_dimension(projected)

    def differing(k):
        exists = exact_sat(pair_file(n, clauses, order, pins, k))
        assert exists == (len({w[:k] for w in survivors}) > 1)
        stats['pair_files'] += 1
        return exists

    while differing(len(order)):
        low, high = 0, len(order)
        while high - low > 1:
            mid = (high + low) // 2
            if differing(mid):
                high = mid
            else:
                low = mid
        pins.append(high - 1)
        kept = [w for w in survivors if not w[high - 1]]
        assert kept and affine_dimension(kept) < affine_dimension(survivors)
        survivors = kept
        stats['disagreement_rounds'] += 1
    assert len(pins) <= start_dimension and survivors == projected[:1]
    # Recover each site bit by one SAT call with just the discovered zero pins.
    pinned_vars = tuple(order[i] for i in pins)
    recovered = tuple(exact_sat(inner_file(n, clauses, (*pinned_vars, pos),
                                          (False,) * len(pins) + (True,))) for pos in order)
    assert recovered == projected[0]
    stats['singleton_bit_files'] += len(order)


def evaluates(clauses, assignment):
    return all(any(assignment[abs(lit) - 1] == (lit > 0) for lit in row) for row in clauses)


def audit_case(n, clauses, order, stats):
    assert len(order) == len(set(order)) and all(0 <= p < n for p in order)
    models = [word for word in words(n) if evaluates(clauses, word)]
    projected = sorted({tuple(word[i] for i in order) for word in models})
    assert exact_sat(dimacs(n, clauses)) == bool(projected)
    stats['families'] += 1
    stats['unsat'] += not bool(projected)
    stats['multiple_projections'] += len(projected) > 1
    stats['projection_ties'] += len(models) > len(projected)

    completions = {}
    for length in range(len(order) + 1):
        for prefix in words(length):
            exists = exact_sat(inner_file(n, clauses, order, prefix=prefix))
            assert exists == any(word[:length] == prefix for word in projected)
            completions[prefix] = exists
            stats['prefix_files'] += 1

    # Each candidate below has two independent certificates of minimality:
    # one failed strict-comparison query, or the failed zero branches for
    # its one bits. Both also require the candidate to extend to a model.
    accepted = []
    for candidate in words(len(order)):
        smaller = exact_sat(inner_file(n, clauses, order, less_than=candidate))
        assert smaller == any(word < candidate for word in projected)
        excluded = [not completions[candidate[:i] + (False,)]
                    for i, bit in enumerate(candidate) if bit]
        assert (not smaller) == all(excluded)
        if completions[candidate] and not smaller:
            accepted.append(candidate)
        stats['strict_files'] += 1
    assert accepted == projected[:1]

    # Sites may ask either literal of a coordinate. Each existential answer
    # uses a full accepted candidate and then imposes its own coordinate.
    for index in range(len(order)):
        for bit in (False, True):
            got = any(w[index] == bit for w in accepted)
            assert got == (bool(projected) and projected[0][index] == bit)
            stats['coordinate_queries'] += 1

    if projected:
        recover_by_disagreements(n, clauses, order, projected, stats)
        path = ()
        for _ in order:
            path += (not completions[path + (False,)],)
        assert accepted == [path]
        # Independent per-coordinate existential queries can combine several
        # valid witnesses into a word with no satisfying extension.
        union = tuple(any(w[i] for w in projected) for i in range(len(order)))
        stats['invalid_coordinate_unions'] += union not in projected
    return accepted


def exclude(word):
    return tuple(-(i + 1) if value else i + 1 for i, value in enumerate(word))


def repeated_word_family(dimension, forced, copies):
    """All words 0^forced x x ... x, for x in the dimension-bit cube."""
    clauses = [exclude(pattern) for pattern in words(3) if any(pattern)]
    for variable in range(4, 4 + forced):
        clauses.append((-variable, 1, 2))  # anchors 1, 2 and 3 are false
    first = 4 + forced
    for j in range(1, copies):
        for k in range(dimension):
            root = first + k
            replica = root + j * dimension
            clauses.extend(((-root, replica, 1), (root, -replica, 1)))
    n = 3 + forced + copies * dimension
    order = tuple(range(3, n))
    expected = [(False,) * forced + x * copies for x in words(dimension)]
    assert all(evaluates(clauses, (False, False, False) + row) for row in expected)
    assert affine_dimension(expected) == dimension
    stats = Counter()
    recover_by_disagreements(n, clauses, order, expected, stats)
    assert stats['disagreement_rounds'] == dimension
    return len(order), len(expected), stats


def main():
    stats = Counter()
    cube = list(words(3))
    for mask in range(256):
        # All 256 possible sets of satisfying 3-bit words have a proper
        # 3-CNF, one clause forbidding each unwanted assignment.
        clauses = [exclude(w) for i, w in enumerate(cube) if mask & (1 << i)]
        audit_case(3, clauses, (0, 1, 2), stats)

    # These two allowed witnesses have different first and last bits. Their
    # independent coordinate-wise OR violates the physical source formula.
    pair = {(False, True, True), (True, True, False)}
    ambiguous = [exclude(w) for w in cube if w not in pair]
    assert audit_case(3, ambiguous, (0, 1, 2), stats) == [(False, True, True)]
    assert audit_case(3, ambiguous, (2, 1, 0), stats) == [(False, True, True)]
    assert not evaluates(ambiguous, (True, True, True))

    # Nontrivial clauses, an unconstrained hidden variable, reordered visible
    # coordinates, and empty visible sets exercise all tie conventions.
    clauses = [(1, -2, 3), (-1, 3, 4), (-2, -3, 4), (-1, -3, -4)]
    for order in ((0, 1, 2, 3, 4), (4, 2, 3, 1, 0), (2, 0), ()):
        audit_case(5, clauses, order, stats)
    audit_case(3, [exclude(w) for w in cube], (), stats)
    assert stats['invalid_coordinate_unions'] and stats['projection_ties'] and stats['unsat']
    print(" ".join(f"{key}={value}" for key, value in stats.items()))
    length, count, repeated = repeated_word_family(10, 24, 7)
    print(f"repeated_family: bits={length} models={count} dimension=10 "
          + " ".join(f"{key}={value}" for key, value in repeated.items()))


if __name__ == '__main__':
    main()
