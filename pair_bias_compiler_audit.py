"""Local exhaustive checks of the three-share SAT compiler and its bias bounds."""

from collections import defaultdict
from itertools import combinations, product


def parity(word):
    return word.bit_count() & 1


def decode(raw, groups):
    # The physical order uses one bit of every group on each of three rounds.
    return (raw ^ (raw >> groups) ^ (raw >> (2 * groups))) & ((1 << groups) - 1)


def fibers(groups):
    result = defaultdict(list)
    for raw in range(1 << (3 * groups)):
        result[decode(raw, groups)].append(raw)
    return result


def state_word(increments, width):
    state = word = 0
    for edge in range(width):
        word |= state << edge
        state ^= (increments >> edge) & 1
    assert state == 1  # The last successor is the complement of the first state.
    return word


def link(literal, previous, following):
    return ((literal or not previous or following)
            and (literal or previous or not following))


def cycle_count(literals, width):
    result = 0
    for start in (0, 1):
        ways = [int(start == 0), int(start == 1)]
        for edge in range(width):
            literal = (literals >> edge) & 1
            ways = [sum(ways[a] for a in (0, 1) if link(literal, a, b)) for b in (0, 1)]
        result += ways[1 - start]
    return result


def check_local_cycles():
    tested = extensions = 0
    for width in (9, 12):
        for literals in range(1 << width):
            count = cycle_count(literals, width)
            assert count == ((1 << literals.bit_count()) if literals else 0)
            subset = literals
            odd = 0
            while subset:
                if parity(subset):
                    omitted = literals.bit_count() - subset.bit_count()
                    assert omitted >= int(parity(literals) == 0)
                    odd += 1
                subset = (subset - 1) & literals
            assert 2 * odd == count
            if literals:
                choices = [literals & -literals]
                if parity(literals):
                    choices.append(literals)
                for increments in choices:
                    word = state_word(increments, width)
                    states = [(word >> j) & 1 for j in range(width)]
                    for seed in (0, 1):
                        path = [s ^ seed for s in states] + [1 ^ seed]
                        assert all(link((literals >> j) & 1, path[j], path[j+1])
                                   for j in range(width))
            tested += 1
            extensions += count
    return tested, extensions


def check_clauses(tables):
    patterns = decoded_tests = 0
    for bad_source in range(8):
        guarded = not parity(bad_source)
        groups = 4 if guarded else 3
        bad = bad_source | (8 if guarded else 0)
        forbidden = set(tables[groups][bad])
        assert len(forbidden) == (256 if guarded else 64)
        assert all(parity(p) == 1 for p in forbidden)
        for decoded, words in tables[groups].items():
            source = decoded & 7
            expected = source != bad_source or (guarded and not (decoded & 8))
            for raw in words:
                assert (raw not in forbidden) == expected
                decoded_tests += 1
        patterns += len(forbidden)
    return patterns, decoded_tests


def check_source_families():
    cases = 0
    for formula in range(256):
        clauses = [bad for bad in range(8) if formula >> bad & 1]
        permits = []
        for active in (0, 1):
            successes = [source for source in range(8) if all(
                source != bad or (not parity(bad) and not active) for bad in clauses)]
            permits.append(bool(successes))
            if not active:
                assert 0 in successes
        possible = {0}
        for _ in range(8):
            possible = {old ^ flag for old in possible for flag in (0, 1) if permits[flag]}
            assert (1 in possible) == (len(clauses) < 8)
            cases += 1
    # A unique satisfying source whose clause with bad tuple 010 has even
    # literal parity on every active block and has no activation guard.
    bads = set(range(8)) - {1}
    assert [x for x in range(8) if x not in bads] == [1]
    assert 2 in bads and parity(2) == 1 and (1 ^ 2).bit_count() == 2
    return cases


def prefix_characters(groups):
    first = [1 << (2 * j) for j in range(groups)]
    second = [a << 1 for a in first]
    rows = first + second + [a ^ b for a, b in zip(first, second)]
    mask = 0
    prefixes = []
    for row in rows:
        prefixes.append(mask)
        mask ^= row
    assert mask == 0 and len(set(prefixes)) == len(rows)
    assert all(prefixes[a] ^ prefixes[b] for a, b in combinations(range(len(rows)), 2))
    assert len(set(rows)) == len(rows) and all(rows)
    return rows, prefixes


def character_sums(states, width):
    # Pack the values of one state coordinate over all raw samples in a large
    # integer, so that a population count gives its exact pair disagreement.
    columns = [sum(((y >> j) & 1) << i for i, y in enumerate(states)) for j in range(width)]
    return [len(states) - 2 * (a ^ b).bit_count() for a, b in combinations(columns, 2)]


def check_moments(tables):
    local = global_cases = mixtures = 0
    active_moments = {}
    inactive_moments = {}
    for groups in (3, 4):
        width = 3 * groups
        prefix_characters(groups)
        for delta, matches in tables[groups].items():
            if delta == 0:
                continue  # A forbidden decoded tuple gives no block solution.
            active = [state_word(l & -l, width) for l in matches]
            active_sums = character_sums(active, width)
            active_moments[groups, delta] = active_sums
            size = len(matches)
            # Each first/second/third share is unbiased; their distinct masks
            # also force pairwise independence at each fixed decoded tuple.
            raw_sums = character_sums(matches, width)
            assert all(((sum((l >> j) & 1 for l in matches)) * 2 == size)
                       for j in range(width))
            assert all(value == 0 for value in raw_sums)
            if parity(delta):
                inactive = [state_word(l, width) for l in matches]
                inactive_moments[groups, delta] = character_sums(inactive, width)
                assert all(v == 0 for v in inactive_moments[groups, delta])
            # The near-independence cost follows from local conservation:
            # each missing true link yields one unit of slack.
            increments = [l & -l for l in matches]
            correlation_total = sum(width - 2 * h.bit_count() for h in increments)
            literal_total = sum(width - 2 * l.bit_count() for l in matches)
            slack = sum(l.bit_count() - h.bit_count() for l, h in zip(matches, increments))
            assert literal_total == 0 and correlation_total - literal_total == 2 * slack
            assert slack >= (size if not parity(delta) else 0)
            local += 1
    for bad_source in range(8):
        groups = 3 if parity(bad_source) else 4
        bad = bad_source | (8 if groups == 4 else 0)
        inactive = inactive_moments[groups, bad]  # all logical bits zero
        for witness in range(8):
            if witness == bad_source:
                continue
            decoded = witness | (8 if groups == 4 else 0)
            active = active_moments[groups, bad ^ decoded]
            size = len(tables[groups][decoded])
            for blocks in range(1, 9):
                totals = [a + (blocks - 1) * z for a, z in zip(active, inactive)]
                # The denominator of each moment is size * blocks.
                assert all(abs(value) <= size for value in totals)
                if bad_source == 2 and witness == 1:
                    assert max(abs(value) for value in totals) * 9 >= 2 * size
                mixtures += 1
    for groups in range(1, 17):
        prefix_characters(groups)
        if groups > 4:
            continue  # The mask check above works without expanding 4^groups samples.
        for block in range(groups):
            matches = tables[groups][1 << block]
            assert all(parity(raw) for raw in matches)
            states = [state_word(raw, 3 * groups) for raw in matches]
            assert all(v == 0 for v in character_sums(states, 3 * groups))
            global_cases += 1
    # For any fixed raw bits, independent seeds cancel cross-cycle and
    # state/raw characters for every possible pair of fixed phase bits.
    for a, b in product((0, 1), repeat=2):
        assert sum((-1)**(a ^ r ^ b ^ s) for r, s in product((0, 1), repeat=2)) == 0
        assert sum((-1)**(a ^ r ^ b) for r in (0, 1)) == 0
    return local, global_cases, mixtures


def main():
    tables = {g: fibers(g) for g in range(1, 5)}
    cycles, assignments = check_local_cycles()
    patterns, rows = check_clauses(tables)
    families = check_source_families()
    local, activations, mixtures = check_moments(tables)
    print(f"{patterns} forbidden patterns, {rows} raw clause evaluations, "
          f"{cycles} full cycle truth tables with {assignments} satisfying extensions, "
          f"{families} source-family/block counts, {local} nonzero local parity fibers, "
          f"{activations} global single-activation fibers, {mixtures} clause mixtures; "
          f"interval masks through 16 groups")


if __name__ == "__main__":
    main()
