"""Check semantic successor payloads and destination-only sensitivity in explicit 3-CNFs."""

from collections import Counter
from itertools import combinations, permutations

from word_permutation_history_audit import encode_clause, tautology


def edge_clauses(source, target, parity):
    """The pair enforces x_source XOR x_target = parity. CNF variable names start at 1."""
    x, y = source + 1, target + 1
    if parity:
        return ((x, y, y), (-x, -y, -y))
    return ((-x, y, y), (x, -y, -y))


def satisfying_columns(count):
    """One bit for each Boolean assignment. Evaluate the actual disjunctions."""
    all_assignments = (1 << (1 << count)) - 1
    literal = {}
    for i in range(count):
        column = sum(1 << mask for mask in range(1 << count) if mask & (1 << i))
        literal[i + 1] = column
        literal[-(i + 1)] = all_assignments ^ column

    columns = {}
    for i in range(count):
        for j in range(count):
            for parity in (0, 1):
                clauses = edge_clauses(i, j, parity)
                result = all_assignments
                for first, second, third in clauses:
                    result &= literal[first] | literal[second] | literal[third]
                different = literal[i + 1] ^ literal[j + 1]
                assert result == (different if parity else all_assignments ^ different)
                columns[i, j, parity] = result
    return all_assignments, columns


def check_words(count):
    """A rewiring changes only the four encoded copies of its destination field."""
    width = max(5, count.bit_length() + 2)
    stride = 3 * width
    guard = encode_clause(tautology((1 << (width - 1)) - 1), width)
    filler = encode_clause(tautology(1), width)
    comparisons = 0
    for sign in (0, 1):
        for source in range(count):
            for phase in range(stride):
                words = []
                for target in range(count):
                    clauses = edge_clauses(source, target, sign)
                    body = ''.join(encode_clause(c, width) for c in clauses) + filler
                    word = guard[phase:] + body + guard[:phase]
                    assert len(word) == 12 * width
                    first = stride - phase
                    for slot in (0, 3):
                        pos = first + slot * width + 1
                        assert int(word[pos:pos + width - 1], 2) == source + 1
                    for slot in (1, 2, 4, 5):
                        pos = first + slot * width + 1
                        assert int(word[pos:pos + width - 1], 2) == target + 1
                    words.append(int(word, 2))
                for a, b in combinations(range(count), 2):
                    logical = ((a + 1) ^ (b + 1)).bit_count()
                    assert (words[a] ^ words[b]).bit_count() == 4 * logical
                    comparisons += 1
    return comparisons


def cycle_nodes_after_rewire(successors, source, target):
    """Remove source's old edge, point it to target, and find all cycles independently."""
    following = successors.copy()
    following[source] = target
    finished = set()
    cyclic = []
    for start in range(len(following)):
        if start in finished:
            continue
        current = start
        position = {}
        path = []
        while current not in finished and current not in position:
            position[current] = len(path)
            path.append(current)
            current = following[current]
        if current in position:
            cyclic.append(path[position[current]:])
        finished.update(path)
    assert len(cyclic) == 1
    return cyclic[0]


def check_cycles(count):
    all_assignments, columns = satisfying_columns(count)
    labels = range(count)
    pairs = list(combinations(labels, 2))
    neighbors = [(i, j) for i, j in pairs if ((i + 1) ^ (j + 1)).bit_count() == 1]
    total_cycles = 0
    total_rewires = 0
    minimum_distances = Counter()
    nonself_minimum = Counter()
    for rest in permutations(range(1, count)):
        order = (0, *rest)
        successors = [0] * count
        for i, j in zip(order, order[1:] + order[:1]):
            successors[i] = j
        for mark_count in (3, 4):
            signs = [int(i < mark_count) for i in labels]
            original_yes = mark_count % 2 == 0
            equations = [columns[i, j, signs[i]] for i, j in enumerate(successors)]
            prefix = [all_assignments]
            for truth in equations:
                prefix.append(prefix[-1] & truth)
            assert prefix[-1].bit_count() == (2 if original_yes else 0)
            suffix = [all_assignments] * (count + 1)
            for i in reversed(labels):
                suffix[i] = equations[i] & suffix[i + 1]

            # A color at j is the XOR on the fixed ordered prefix before j.
            color = {}
            parity = 0
            for i in order:
                color[i] = parity
                parity ^= signs[i]
            flips = set()
            for source, old in enumerate(successors):
                other_equations = prefix[source] & suffix[source + 1]
                assert other_equations.bit_count() == 2
                arc_parity = signs[old]
                target = successors[old]
                distances = []
                nonself = []
                while target != old:
                    after = other_equations & columns[source, target, signs[source]]
                    flipped = bool(after) != original_yes
                    assert after.bit_count() in (0, 2)
                    assert flipped == bool(arc_parity)
                    if flipped:
                        flips.add((old, target))
                        bits = ((old + 1) ^ (target + 1)).bit_count()
                        distances.append(bits)
                        if target != source:
                            nonself.append(bits)
                        # Independently validate actual graph topology for a witness.
                        if len(nonself) == 1 and target != source:
                            cycle = cycle_nodes_after_rewire(successors, source, target)
                            assert len(cycle) >= 2
                            assert bool(after) == (sum(signs[v] for v in cycle) % 2 == 0)
                    total_rewires += 1
                    arc_parity ^= signs[target]
                    target = successors[target]
                assert distances and nonself
                minimum_distances[mark_count, min(distances)] += 1
                nonself_minimum[mark_count, min(nonself)] += 1

            for i, j in pairs:
                orientation_count = int((i, j) in flips) + int((j, i) in flips)
                expected = 2 * int(color[i] != color[j]) if original_yes else 1
                assert orientation_count == expected
            if not original_yes:
                assert len(flips) == len(pairs)
                assert sum(int((i, j) in flips) + int((j, i) in flips)
                           for i, j in neighbors) == len(neighbors)
            total_cycles += 1
    return total_cycles, total_rewires, minimum_distances, nonself_minimum


def anchored_clauses(base, source, target, parity, split):
    x = 1 if split and source == 0 else base + source
    y = base + target
    if parity:
        return ((x, x, y), (-x, -x, -y))
    return ((-x, -x, y), (x, x, -y))


def check_single_bit_mutations(count, split=False):
    """Evaluate each one-occurrence low bit change, retaining the pinned variable."""
    bits = (count - 1).bit_length()
    assert count == 1 << bits
    base = count
    width = (2 * count - 1).bit_length() + 1
    names = list(range(base, base + count)) + ([1, 2] if split else [])
    assignments = 1 << len(names)
    all_assignments = (1 << assignments) - 1
    literal = {}
    for i, name in enumerate(names):
        column = sum(1 << mask for mask in range(assignments) if mask & (1 << i))
        literal[name] = column
        literal[-name] = all_assignments ^ column
    if split:
        # Y is named 1 and Z is named 2. The only changed literal in the paired inputs
        # is the sign of Y in this fixed clause. Z is pinned false separately.
        pin_pair = ((-1, 2, 2), (1, 2, 2))
        left, right = (int(encode_clause(c, width), 2) for c in pin_pair)
        assert (left ^ right).bit_count() == 1

    def truth(clause):
        a, b, c = clause
        return literal[a] | literal[b] | literal[c]

    trials = mutations = 0
    flips = Counter()
    for serial, rest in enumerate(permutations(range(1, count))):
        if count == 8 and serial % 37:
            continue
        # The marked outgoing edge of 0 wraps from the last to the first position.
        order = (*rest, 0)
        successors = [0] * count
        for i, j in zip(order, order[1:] + order[:1]):
            successors[i] = j
        for negative in (False, True):
            signs = [
                ((i.bit_count() ^ j.bit_count()) & 1) ^ (not split and negative and i == 0)
                for i, j in enumerate(successors)
            ]
            pin = literal[-base]
            if split:
                pin &= literal[-2] & truth(pin_pair[int(negative)])
            clauses = [anchored_clauses(base, i, j, signs[i], split)
                       for i, j in enumerate(successors)]
            if split and not negative:
                positive_word_clauses = clauses
            if split and negative:
                assert clauses == positive_word_clauses
            equation = [truth(left) & truth(right) for left, right in clauses]
            original = pin
            for allowed in equation:
                original &= allowed
            assert original.bit_count() == int(not negative)
            observed_total = 0
            for index, old in enumerate(order):
                source = order[index - 1]
                others = pin
                for i, allowed in enumerate(equation):
                    if i != source:
                        others &= allowed
                # The path plus the pin leaves precisely one whole assignment.
                assert others.bit_count() == 1
                unique_mask = others.bit_length() - 1
                for rank, v in enumerate(order):
                    expected_bit = (v.bit_count() & 1) ^ (negative and rank < index)
                    assert ((unique_mask >> v) & 1) == expected_bit
                if split:
                    assert (unique_mask >> count) & 1 == int(negative)
                    assert not (unique_mask >> (count + 1)) & 1
                    sign_hits = 0
                    for lane in (0, 1):
                        before = clauses[source][lane]
                        changed = (*before[:2], -before[-1])
                        words = [int(encode_clause(c, width), 2) for c in (before, changed)]
                        assert (words[0] ^ words[1]).bit_count() == 1
                        result = others & truth(clauses[source][1 - lane]) & truth(changed)
                        sign_hits += bool(result) != bool(original)
                    assert sign_hits == 1
                for bit in range(bits):
                    target = old ^ (1 << bit)
                    sensitive_lanes = 0
                    for lane in (0, 1):
                        old_clause = clauses[source][lane]
                        signed = old_clause[-1]
                        new_name = (1 if signed > 0 else -1) * (base + target)
                        changed = (*old_clause[:2], new_name)
                        raw_before = int(encode_clause(old_clause, width), 2)
                        raw_after = int(encode_clause(changed, width), 2)
                        assert raw_before ^ raw_after == 1 << bit
                        result = others & truth(clauses[source][1 - lane]) & truth(changed)
                        sensitive_lanes += bool(result) != bool(original)
                        mutations += 1
                    expected = not negative or index < order.index(target)
                    assert sensitive_lanes == int(expected)
                    observed_total += sensitive_lanes
            expected_total = count * bits // (2 if negative else 1)
            assert observed_total == expected_total
            flips[negative] += observed_total
            trials += 1
    return trials, mutations, flips


if __name__ == "__main__":
    total_signings = total_changes = total_fields = 0
    minimum = Counter()
    nonself = Counter()
    for n in range(4, 9):
        signed_cycles, rewires, distances, nonself_distances = check_cycles(n)
        total_signings += signed_cycles
        total_changes += rewires
        total_fields += check_words(n)
        minimum.update(distances)
        nonself.update(nonself_distances)
    print(f"{total_signings:,} signed Hamiltonian cycles and {total_changes:,} "
          "destination-only rewires checked against all assignments")
    print(f"{total_fields:,} packed-word Hamming distances checked across all guard phases")
    for marks in (3, 4):
        distances = {d: c for (m, d), c in sorted(minimum.items()) if m == marks}
        proper = {d: c for (m, d), c in sorted(nonself.items()) if m == marks}
        print(f"{marks} marked sources, one-based minimum field-bit changes {distances}, "
              f"excluding self-loops {proper}")
    for n in (4, 8):
        for split in (False, True):
            cases, changes, flips = check_single_bit_mutations(n, split)
            model = "split source" if split else "marked edge"
            print(f"{n} vertices, {model}, {cases} signed cycles, {changes:,} individual "
                  f"field-bit mutations, YES flips {flips[False]:,}, NO flips {flips[True]:,}")
