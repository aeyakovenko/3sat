"""Finite checks for the number of fair coins needed to color the first feasible row."""

from itertools import groupby, product


def color_runs(colors):
    end = 0
    result = []
    for color, group in groupby(colors):
        end += len(tuple(group))
        result.append((color, end))
    return result


def compile_tapes(colors, odds):
    """Return batches (color, prefix length, multiplicity) of disjoint public tags."""
    current = [0, 0]
    batches = []
    for color, end in reversed(color_runs(colors)):
        target = max(1, odds * current[1 - color])
        increment = target - current[color]
        assert increment > 0
        batches.append((color, end, increment))
        current[color] = target
    return batches


def required_tapes(runs, odds):
    return 1 if runs == 1 else (odds + 1) * odds ** (runs - 2)


def surviving_counts(feasible, batches):
    counts = [0, 0]
    for color, end, multiplicity in batches:
        if feasible & ((1 << end) - 1):
            counts[color] += multiplicity
    return counts


def check_all_inputs():
    lists = inputs = 0
    for length in range(1, 8):
        for colors in product((0, 1), repeat=length):
            runs = len(color_runs(colors))
            for odds in (2, 3, 4, 5):
                batches = compile_tapes(colors, odds)
                total = sum(multiplicity for _, _, multiplicity in batches)
                assert total == required_tapes(runs, odds)
                coins = (total - 1).bit_length()
                assert total <= 1 << coins
                assert coins == 0 or 1 << (coins - 1) < total
                # Unused tapes never survive. Empty availability has no first item.
                assert surviving_counts(0, batches) == [0, 0]
                for feasible in range(1, 1 << length):
                    first = (feasible & -feasible).bit_length() - 1
                    color = colors[first]
                    counts = surviving_counts(feasible, batches)
                    assert counts[color] > 0 and counts[color] >= odds * counts[1 - color]
                    inputs += 1
                lists += 1
    return lists, inputs


def can_follow_suffix_chain(colors, odds, budget):
    """Exhaust monotone integer score pairs on successive nested nonempty suffixes."""
    size = budget + 1
    reachable = {(0, 0)}
    for color in reversed(colors):
        # A pair is permitted iff it weakly increases both previous counts.
        # The grid computes the upward closure of every reachable pair.
        above = [[False] * size for _ in range(size)]
        following = set()
        for zero in range(size):
            for one in range(size - zero):
                above[zero][one] = (
                    (zero, one) in reachable
                    or (zero > 0 and above[zero - 1][one])
                    or (one > 0 and above[zero][one - 1])
                )
                scores = (zero, one)
                if (above[zero][one] and scores[color] > 0
                        and scores[color] >= odds * scores[1 - color]):
                    following.add(scores)
        reachable = following
    return bool(reachable)


def check_monotone_lower_bound():
    cases = 0
    for odds in range(2, 6):
        for runs in range(1, 9):
            required = required_tapes(runs, odds)
            if required > 140:
                continue
            for first in (0, 1):
                alternating = tuple(first ^ (i % 2) for i in range(runs))
                for colors in (alternating, tuple(c for c in alternating for _ in range(2))):
                    assert not can_follow_suffix_chain(colors, odds, required - 1)
                    assert can_follow_suffix_chain(colors, odds, required)
                    cases += 1
    return cases


def check_feasible_run_promise():
    """Witness alternating subsequences when only the surviving run count is small."""
    cases = 0
    for length in range(2, 7):
        for colors in product((0, 1), repeat=length):
            public_runs = len(color_runs(colors))
            for cap in range(1, public_runs):
                for odds in (2, 3):
                    largest_seen = [0, 0]
                    for feasible in range(1, 1 << length):
                        active = [colors[i] for i in range(length) if feasible & (1 << i)]
                        if len(color_runs(active)) > cap:
                            continue
                        largest = [0, 0]
                        for subset in range(1, 1 << len(active)):
                            seq = [v for j, v in enumerate(active) if subset & (1 << j)]
                            if all(a != b for a, b in zip(seq, seq[1:])):
                                largest[seq[0]] = max(largest[seq[0]], len(seq))
                        counts = [odds ** (t - 1) if t else 0 for t in largest]
                        first = active[0]
                        assert counts[first] > 0 and counts[first] >= odds * counts[1 - first]
                        largest_seen[first] = max(largest_seen[first], counts[first])
                        cases += 1
                    assert largest_seen == [odds ** (cap - 1)] * 2
    return cases


if __name__ == '__main__':
    lists, inputs = check_all_inputs()
    print(f'{lists} color lists and odds, covering {inputs} nonempty availability patterns.')
    cases = check_monotone_lower_bound()
    print(f'{cases} suffix chains with exhaustive integer-score tests at both adjacent budgets.')
    print(f'{check_feasible_run_promise()} feasible-run promise cases with subsequence witnesses.')
