"""Exhaust finite calibration protocols and test the two branches of the construction."""

from itertools import product
from random import Random


def dot(word, row):
    return (word & row).bit_count() & 1


def extend(span, row):
    return span | {x ^ row for x in span}


def run(tree, word):
    span = {0}
    trace = []
    wins = 0
    lost = False
    while tree is not None:
        row, guess, left, right = tree
        bit = dot(word, row)
        trace.append((row, bit))
        if guess is not None and row not in span and not lost:
            if bit == guess:
                wins += 1
            else:
                lost = True
        span = extend(span, row)
        tree = right if bit else left
    return tuple(trace), wins


def check_tree(tree, h):
    words = range(1 << h)
    results = [run(tree, word) for word in words]
    for threshold in range(h + 2):
        successes = sum(wins >= threshold for _, wins in results)
        assert successes * (1 << threshold) <= len(words)

    # Agreement on the transcript is both necessary and sufficient to replay it.
    for trace in {t for t, _ in results}:
        compatible = [u for u in words if all(dot(u, x) == bit for x, bit in trace)]
        assert compatible == [u for u in words if results[u][0] == trace]
        span = {0}
        for row, _ in trace:
            span = extend(span, row)
        for query in words:
            forced = len({dot(u, query) for u in compatible}) == 1
            assert forced == (query in span)


def trees():
    h = 2
    moves = list(product(range(1 << h), [None, 0, 1]))
    short = [None] + [(row, guess, None, None) for row, guess in moves]
    count = 0
    for row, guess in moves:
        for left, right in product(short, repeat=2):
            check_tree((row, guess, left, right), h)
            count += 1
    rng = Random(104729)

    def generate(depth):
        if not depth or rng.randrange(8) == 0:
            return None
        return (rng.randrange(16), rng.choice([None, 0, 1]),
                generate(depth - 1), generate(depth - 1))

    for _ in range(100):
        check_tree(generate(6), 4)
    print(f"{count} exhaustive two-step trees and 100 deeper adaptive trees passed")


def history_schedule():
    rng = Random(65537)
    h = 7
    size = 1 << h
    history = []
    retired = set()
    defaults = 0
    differing_counterfactuals = 0
    for stage in range(1, 401):
        advice = 2
        forbidden = set()
        for index in range(6):
            for allowance in [0, advice]:
                for _ in range((1 << (allowance + 1)) - 1):
                    count = rng.randrange(10)
                    mask = set(rng.sample(range(size), count))
                    if (len(mask) << (allowance + index + 4)) <= size:
                        forbidden.update(mask)
        assert 2 * len(forbidden) <= size
        default = next(u for u in range(size) if u not in forbidden)
        last = history[-1][0] if history else 0
        limit = stage.bit_length()
        proposals = []
        for index in range(limit):
            # Past-dependent opportunities and proposed counterexample words.
            row = 1 << (index % h)
            if (stage + last + index) % (2 * index + 3):
                proposals.append(None)
                continue
            calibration_row = ((index + 3) * stage) % size
            observed = dot(last, calibration_row)
            conclusion = dot(last, row)
            compatible_errors = [u for u in range(size)
                                 if dot(u, calibration_row) == observed
                                 and dot(u, row) != conclusion]
            for u in compatible_errors:
                assert dot(u, calibration_row) == observed
                assert dot(u, row) != conclusion
            proposals.append(compatible_errors[0] if compatible_errors else None)
        winner = next((i for i, w in enumerate(proposals)
                       if w is not None and i not in retired), None)
        actual = default if winner is None else proposals[winner]
        if winner is None:
            defaults += 1
            assert actual not in forbidden
        else:
            retired.add(winner)
            differing_counterfactuals += actual != default
            # The proposed hypothetical path and wrong claim both occur on actual.
            row = 1 << (winner % h)
            calibration_row = ((winner + 3) * stage) % size
            assert dot(actual, calibration_row) == dot(last, calibration_row)
            assert dot(actual, row) != dot(last, row)
        history.append((actual, winner))
        assert len(retired) <= limit
    assert differing_counterfactuals and defaults > 380
    print(f"400 stages with {defaults} defaults and {len(retired)} distinct overrides passed")


if __name__ == "__main__":
    trees()
    history_schedule()
