"""Exact finite checks for the overlap coupling, independent block game, and entropy bound."""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import lcm


@dataclass(frozen=True)
class Test:
    queries: tuple
    # Bit n is set iff the local predicate accepts packed reply n (little-endian).
    truth_table: int

    @property
    def addresses(self):
        return tuple(sorted(set(self.queries)))

    def accepts(self, assignment):
        reply = sum(((assignment >> x) & 1) << i for i, x in enumerate(self.queries))
        return bool(self.truth_table & (1 << reply))


def table(n, predicate):
    return sum(int(predicate(x)) << x for x in range(1 << n))


def projection(seed, mask):
    # Keep selected positions in place. Relabeling a bucket has no probabilistic effect.
    return seed & mask


def assignments(addresses):
    """Enumerate only the address bits the table actually returns."""
    addresses = tuple(sorted(set(addresses)))
    for value in range(1 << len(addresses)):
        yield sum(((value >> i) & 1) << x for i, x in enumerate(addresses))


def overlap_kernel(tests, ell):
    """Integer weights with row/column total denominator. Padding always stays at v."""
    n = len(tests)
    occurrences = Counter(x for test in tests for x in test.addresses)
    frequency_multiple = lcm(*occurrences.values())
    denominator = ell * frequency_multiple
    weights = [[0] * n for _ in tests]
    for v, test in enumerate(tests):
        assert len(test.addresses) <= ell
        weights[v][v] += (ell - len(test.addresses)) * frequency_multiple
        for s, other in enumerate(tests):
            for x in set(test.addresses) & set(other.addresses):
                weights[v][s] += frequency_multiple // occurrences[x]
    assert all(sum(row) == denominator for row in weights)
    assert all(sum(column) == denominator for column in zip(*weights))
    return weights, denominator, occurrences, frequency_multiple


def coordinate_marginal_deficit(joint, mask):
    """exp(total mass * conditional KL from a uniform projected sharp-bit string)."""
    alphabet_size = 1 << mask.bit_count()
    result = Fraction(1)
    for row in joint:
        marginal = Counter()
        for seed, multiplicity in enumerate(row):
            marginal[projection(seed, mask)] += multiplicity
        mass = sum(row)
        for count in marginal.values():
            if count:
                result *= Fraction(alphabet_size * count, mass) ** count
    return result


def entropy_test(joint, masks):
    """Compare exponentiated entropies as exact rational numbers."""
    n = len(joint[0])
    assert n & (n-1) == 0
    combined = 0
    product_deficit = Fraction(1)
    for mask in masks:
        assert not combined & mask and mask < n
        combined |= mask
        product_deficit *= coordinate_marginal_deficit(joint, mask)
    full_deficit = coordinate_marginal_deficit(joint, n - 1)
    assert product_deficit <= full_deficit
    return product_deficit == full_deficit


def conditional_joint(tests, block_size, weights):
    n = len(tests)
    return [[sum(weights[v][s] for v in range(first, first+block_size))
             for s in range(n)] for first in range(0, n, block_size)]


def panel_distributions(joint, mask):
    """Distribution of (block, h(s)) and its distance to independent uniform parts."""
    n = len(joint[0])
    buckets = sorted({projection(s, mask) for s in range(n)})
    mass = sum(map(sum, joint))
    grouped = [[sum(count for s, count in enumerate(row) if projection(s, mask) == bucket)
                for bucket in buckets] for row in joint]
    outcomes = len(joint) * len(buckets)
    deviation = sum(abs(count*outcomes - mass) for row in grouped for count in row)
    return grouped, Fraction(deviation, 2*mass*outcomes)


def audit_game(name, tests, block_size, ell, masks):
    n = len(tests)
    assert n & (n-1) == 0 and n % block_size == 0 and block_size > 0
    assert all(mask.bit_count() == masks[0].bit_count() for mask in masks)
    weights, denominator, degrees, multiple = overlap_kernel(tests, ell)
    mass = n * denominator
    blocks = [range(first, first+block_size) for first in range(0, n, block_size)]
    direct_weights = [[denominator * int(i == s) for s in range(n)] for i in range(n)]
    distributions = [conditional_joint(tests, block_size, w) for w in (weights, direct_weights)]
    for joint in distributions:
        for row in joint:
            assert max(row)*block_size <= sum(row)
        entropy_test(joint, [1 << k for k in range((n-1).bit_length())])
        assert coordinate_marginal_deficit(joint, n-1) <= (n // block_size)**mass

    proof_addresses = sorted(degrees)
    delta = Fraction(min(sum(not t.accepts(word) for t in tests)
                         for word in assignments(proof_addresses)), n)

    panels = []
    for mask in masks:
        coupled, tv_coupled = panel_distributions(distributions[0], mask)
        direct, tv_direct = panel_distributions(distributions[1], mask)
        buckets = sorted({projection(s, mask) for s in range(n)})
        right_options = []
        for key in buckets:
            addresses = sorted({z for s, test in enumerate(tests) if projection(s, mask) == key
                                for z in test.addresses})
            right_options.append((sum(1 << z for z in addresses), list(assignments(addresses))))
        panels.append((coupled, direct, tv_coupled, tv_direct, right_options, buckets))

    tv1 = sum(panel[2] for panel in panels) / len(panels)
    tv2 = sum(panel[3] for panel in panels) / len(panels)
    lower = delta/(4*ell) - (tv1+tv2)/2
    best_game = Fraction(1)
    nleft = 0
    all_right_totals = 0
    mixed_local = 0
    address_masks = [sum(1 << z for z in test.addresses) for test in tests]
    for left in product(*(list(assignments(t.addresses)) for t in tests)):
        local_bad = [not t.accepts(word) for t, word in zip(tests, left)]
        block_bad = [any(local_bad[v] for v in block) for block in blocks]
        mixed_local += int(any(local_bad) and not all(local_bad))
        minority = 0
        disagrees = 0
        for z, degree in degrees.items():
            ones = sum((left[v] >> z) & 1 for v in range(n) if z in tests[v].addresses)
            minority += min(ones, degree-ones)
            disagrees += 2*ones*(degree-ones)*(multiple // degree)
        discordance = Fraction(disagrees, mass)
        # Rounding to an address majority can spoil no more than one row per changed slot.
        assert delta <= Fraction(sum(local_bad) + minority, n)
        assert Fraction(minority, n*ell) <= discordance

        independent = coupled_reject = direct_reject = Fraction(0)
        for mask, (coupled, direct, t1, t2, options, buckets) in zip(masks, panels):
            rates = []
            possible_totals = {(0, 0, 0)}
            for key_index, (bucket_mask, answers) in enumerate(options):
                key = buckets[key_index]
                possible_column = set()
                best_column = None
                for right in answers:
                    rejected = [bad or any((left[v] ^ right) & address_masks[v] & bucket_mask
                                           for v in block)
                                for block, bad in zip(blocks, block_bad)]
                    # This holds for every possible right reply, before optimizing it.
                    for s in range(n):
                        if projection(s, mask) != key:
                            continue
                        for v in range(n):
                            if (left[v] ^ left[s]) & address_masks[v] & address_masks[s]:
                                assert rejected[v // block_size] or rejected[s // block_size]
                    statistics = (sum(rejected),
                                  sum(coupled[i][key_index] for i, bad in enumerate(rejected) if bad),
                                  sum(direct[i][key_index] for i, bad in enumerate(rejected) if bad))
                    possible_column.add(statistics)
                    if best_column is None or statistics[0] < best_column[0]:
                        best_column = statistics
                rates.append(best_column)
                possible_totals = {(a+d, b+e, c+f) for a, b, c in possible_totals
                                   for d, e, f in possible_column}
            # These triples cover all deterministic right tables for this public
            # projection, including every nonoptimal way to trade the two laws.
            cells = len(blocks) * len(buckets)
            for rejects, via_weight, direct_weight in possible_totals:
                p = Fraction(rejects, cells)
                assert disagrees <= via_weight + direct_weight
                assert abs(Fraction(via_weight, mass) - p) <= t1
                assert abs(Fraction(direct_weight, mass) - p) <= t2
            all_right_totals += len(possible_totals)
            ind = Fraction(sum(r[0] for r in rates), len(blocks)*len(buckets))
            via = Fraction(sum(r[1] for r in rates), mass)
            diag = Fraction(sum(r[2] for r in rates), mass)
            assert discordance <= via + diag
            assert abs(ind-via) <= t1 and abs(ind-diag) <= t2
            independent += ind
            coupled_reject += via
            direct_reject += diag
        independent /= len(panels)
        coupled_reject /= len(panels)
        direct_reject /= len(panels)
        assert discordance <= coupled_reject + direct_reject
        assert independent >= Fraction(sum(local_bad), n)
        assert independent >= lower
        assert (1+2*ell)*independent >= delta - ell*(tv1+tv2)
        best_game = min(best_game, independent)
        nleft += 1
    assert mixed_local and nleft
    assert delta or best_game == 0
    print(f"{name}: {nleft} left strategies, {all_right_totals} distinct rate triples "
          f"summed across left strategies and projections, delta={delta}, p={best_game}, bound={lower}")
    print("  (mask, TV via overlap, TV direct):",
          ", ".join(f"({mask}, {p[2]}, {p[3]})" for mask, p in zip(masks, panels)))
    return best_game, lower


def partition_audit():
    # Exhaust every binary block label on all 3-bit seeds, including unbalanced ones.
    checked = tight = 0
    for labels in range(256):
        joint = [[int(((labels >> s) & 1) == b) for s in range(8)] for b in (0, 1)]
        for partition in ((1, 2, 4), (3, 4), (5, 2), (6, 1)):
            tight += entropy_test(joint, partition)
            checked += 1
    # Complementary bits reveal no information about their XOR separately.
    parity = [[int((s.bit_count() & 1) == b) for s in range(4)] for b in (0, 1)]
    assert coordinate_marginal_deficit(parity, 1) == coordinate_marginal_deficit(parity, 2) == 1
    assert coordinate_marginal_deficit(parity, 3) == 2**4
    print(f"Disjoint projection partitions: {checked} checked, {tight} tight")


def informed_block_feasible(tests, buckets):
    """Alice fixes her local labels before Bob sees the bucket and the block."""
    local_options = [[word for word in assignments(t.addresses) if t.accepts(word)]
                     for t in tests]
    masks = [sum(1 << x for x in t.addresses) for t in tests]
    right_options = [(sum(1 << x for x in bucket), list(assignments(bucket)))
                     for bucket in buckets]
    for left in product(*local_options):
        if all(any(all((local ^ right) & mask & bucket_mask == 0
                       for local, mask in zip(left, masks))
                   for right in answers)
               for bucket_mask, answers in right_options):
            return True
    return False


def information_order_audit():
    # Overlap of two local predicates on one address; exhaust their truth tables.
    covers = [((0, 1, 2),), ((0,), (1,), (2,)), ((0, 1), (1, 2))]
    counts = Counter()
    for first, second in product(range(16), repeat=2):
        tests = [Test((0, 1), first), Test((1, 2), second)]
        feasible = any(all(t.accepts(word) for t in tests) for word in assignments(range(3)))
        for cover in covers:
            assert informed_block_feasible(tests, cover) == feasible
            counts[feasible] += 1
    # A missing address can conceal a contradiction even within a single block.
    conflict = [Test((0,), 1), Test((0,), 2)]
    assert informed_block_feasible(conflict, ((1,),))
    assert not informed_block_feasible(conflict, ((0,), (1,)))
    print(f"Informed block feasibility: {counts[True]} feasible, {counts[False]} infeasible")

    configurations = checked_blocks = proof_tables = 0
    for r, k in ((3, 1), (3, 2), (4, 2)):
        n = 1 << r
        for missing in range(k, r):
            # A prefix coordinate is frozen on every consecutive size-2^k block.
            low_mask = (1 << missing) - 1
            tests = []
            for seed in range(n):
                address = (seed & low_mask) | ((seed >> (missing+1)) << missing)
                required = (seed >> missing) & 1
                tests.append(Test((address,), 1 << required))
            blocks = [tests[i:i+(1 << k)] for i in range(0, n, 1 << k)]
            addresses = range(n // 2)
            best_uninformed = 0
            for word in assignments(addresses):
                assert sum(t.accepts(word) for t in tests) == n // 2
                # For a sole right bucket containing all addresses, a block passes
                # with this common Bob reply iff its whole conjunction holds.
                successes = sum(all(t.accepts(word) for t in block) for block in blocks)
                best_uninformed = max(best_uninformed, successes)
                proof_tables += 1
            assert 2*best_uninformed == len(blocks)
            covers = [(addresses,), [(x,) for x in addresses]]
            assert all(informed_block_feasible(block, cover) for block in blocks for cover in covers)
            checked_blocks += len(blocks)
            configurations += 1
    print(f"Missing frozen bit: {configurations} seed/block/bit choices, {proof_tables} "
          f"global proof tables correct on exactly half; all {checked_blocks} blocks feasible")


if __name__ == "__main__":
    equality = table(2, lambda x: x in (0, 3))
    inequality = table(2, lambda x: x in (1, 2))
    shared = [Test((0, 1), t) for t in (equality, equality, inequality, inequality)]
    best, lower = audit_game("Two shared addresses", shared, 2, 2, (1,))
    assert best == Fraction(1, 2) and lower == Fraction(1, 16)
    duplicate = table(3, lambda x: x in (3, 4))
    uneven = [Test((0, 1), equality), Test((0, 0, 1), duplicate),
              Test((1, 2), inequality), Test((2,), 2)]
    audit_game("Repeated read and padded degrees", uneven, 2, 3, (1, 2))
    conflict = [Test((0, 1), table(2, lambda x: x < 2)),
                Test((0, 0, 1), table(3, lambda x: x >= 4)),
                Test((1, 2), table(2, lambda x: x < 2)), Test((2,), 2)]
    _, nonzero_tv_bound = audit_game("Positive bound with imperfect mixing", conflict, 2, 3, (1,))
    assert nonzero_tv_bound == Fraction(1, 72)
    wide_masks = [Test((s % 3,), 1 if s < 4 else 2) for s in range(8)]
    audit_game("Two-bit bucket indices", wide_masks, 4, 1, (3, 5, 6))
    consistent = [Test((0,), 1), Test((1,), 2), Test((0,), 1), Test((1,), 2)]
    audit_game("Perfect completeness", consistent, 2, 1, (1,))
    partition_audit()
    information_order_audit()
