"""Exact probabilities for online repairs of a fallible word predictor.

The request, prediction, memory addresses and next work cost can all depend on
earlier *emitted* answers. The simulator always computes them on its own path.
Run with Python 3; no packages beyond the standard library.
"""

from fractions import Fraction
from itertools import product
from math import comb


def step(hidden, alphabet, history):
    t = len(history)
    previous = history[-1] if history else 0
    checksum = sum((i+1)*value for i, value in enumerate(history))
    request = (t + previous) % alphabet
    guess = (2*request + checksum + 1) % alphabet
    answer = (hidden[t] + request) % alphabet
    # A literal ordered list of probes, including an output-dependent follow-up.
    def probes(emitted):
        count = 1 + (request + emitted + checksum) % 4
        return tuple((request + 3*i + previous + emitted) % (2*alphabet+1) for i in range(count))
    return request, guess, answer, probes


def truthful_run(hidden, v):
    history, trace, errors = [], [], []
    for t in range(len(hidden)):
        request, guess, answer, probes = step(hidden, v, history)
        trace.append((request, guess, answer, probes(answer)))
        if guess != answer:
            errors.append(t)
        history.append(answer)
    return trace, errors


def explore(hidden, v, marked, different, reference, errors, budget=None):
    """Branch on the hypergeometric inclusion choice and the proposed symbol."""
    q = len(hidden)
    total_mass = success_mass = Fraction()
    divergent_requests = False
    divergent_workloads = False

    def visit(history, flags, trace, left, prob, spent):
        nonlocal total_mass, success_mass, divergent_requests, divergent_workloads
        t = len(history)
        if budget is not None and spent > budget:
            total_mass += prob
            return
        if t == q:
            assert left == 0
            total_mass += prob
            if all(out == expected[2] for out, expected in zip(history, reference)):
                assert trace == reference and errors <= flags
                if different:
                    assert errors == flags
                success_mass += prob
            return
        request, guess, truth, probes = step(hidden, v, history)
        divergent_requests |= request != reference[t][0]
        n = q-t

        def emit(symbol, chosen, weight):
            nonlocal divergent_workloads
            row = (request, guess, truth, probes(symbol))
            divergent_workloads |= row[3] != reference[t][3]
            visit(history + [symbol], flags | ({t} if chosen else set()), trace + [row],
                  left - int(chosen), prob*weight, spent+len(row[3]))

        if left < n:
            emit(guess, False, Fraction(n-left, n))
        if left:
            guesses = [a for a in range(v) if not different or a != guess]
            for a in guesses:
                emit(a, True, Fraction(left, n*len(guesses)))

    visit([], set(), [], marked, Fraction(1), 0)
    assert total_mass == 1
    return success_mass, divergent_requests, divergent_workloads


def main():
    cases = priors = possible_sizes = 0
    changed_request = changed_work = truncated_checks = 0
    for v, q in [(2, 4), (3, 4), (4, 3)]:
        seen_errors = set()
        for hidden in product(range(v), repeat=q):
            trace, error_list = truthful_run(hidden, v)
            errors = set(error_list)
            e = len(errors)
            seen_errors.add(e)
            probs = [[], []]
            costs = sum(len(row[3]) for row in trace)
            for j in range(q+1):
                for different in (False, True):
                    p, new_request, new_work = explore(hidden, v, j, different, trace, errors)
                    changed_request += int(new_request)
                    changed_work += int(new_work)
                    if different:
                        expected = Fraction(1, comb(q,e)*(v-1)**e) if j == e else 0
                    else:
                        expected = (Fraction(comb(q-e,j-e), comb(q,j)*v**j) if j >= e else 0)
                    assert p == expected
                    probs[different].append(p)
                    cases += 1
            for budget in (costs-1, costs):
                capped, _, _ = explore(hidden, v, e, True, trace, errors, budget=budget)
                assert capped == (probs[1][e] if budget >= costs else 0)
                truncated_checks += 1
            for r in range(q+1):
                ordinary = sum(probs[0][:r+1]) / (r+1)
                excluded = sum(probs[1][:r+1]) / (r+1)
                volume = sum(comb(q,j)*(v-1)**j for j in range(r+1))
                uniform_ball = sum(comb(q,j)*(v-1)**j * probs[1][j] for j in range(r+1))/volume
                if e <= r:
                    assert ordinary >= Fraction(1, (r+1)*comb(q,e)*v**e)
                    assert excluded == Fraction(1, (r+1)*comb(q,e)*(v-1)**e)
                    assert uniform_ball == Fraction(1, volume)
                else:
                    assert ordinary == excluded == uniform_ball == 0
                priors += 3
        assert seen_errors == set(range(q+1))
        possible_sizes += len(seen_errors)
    assert changed_request and changed_work
    print(f"{cases} exact conditional score distributions, {priors} mixed-prior success tests, "
          f"{possible_sizes} truthful mistake-count strata, {truncated_checks} truncated work tests")
    print(f"{changed_request} enumerations reached a different request after hypothetical guesses; "
          f"{changed_work} reached a different genuine work trace. Every successful path exactly "
          "replayed the truthful requests and work.")


if __name__ == "__main__":
    main()
