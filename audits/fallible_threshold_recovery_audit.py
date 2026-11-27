"""Check the finite threshold strategy, exact black-box costs and comparator CNF."""

from functools import lru_cache
from itertools import combinations, product
from random import Random


def majority_search(models, actual, witnesses):
    candidates = len(actual)
    size = len(actual[0]) - 1
    live = models
    failures = questions = verifications = 0
    for row in range(candidates):
        while True:
            prior = live
            prediction = [2 * sum(m[row][i] for m in prior) > len(prior)
                          for i in range(size + 1)]
            if prediction[size]:
                point = next(j for j in range(size) if not prediction[j] and prediction[j+1])
                tests = [point, point+1] if point else [1]
            else:
                point = None
                tests = [size]
            agree = True
            for t in tests:
                questions += 1
                answer = actual[row][t]
                live = [m for m in live if m[row][t] == answer]
                if answer != prediction[t]:
                    agree = False
                    break
            assert actual in live
            if not agree:
                assert 2*len(live) <= len(prior)
                failures += 1
                continue
            if point is not None:
                verifications += 1
                if point in witnesses:
                    return True, failures, questions, verifications
            break
    return False, failures, questions, verifications


def check_joint_models():
    rng = Random(144)
    size = 3
    rows = [(False,) + bits for bits in product((False, True), repeat=size)]
    tables = list(product(rows, repeat=2))
    groups = [tables] + [rng.sample(tables, length) for length in range(1, len(tables)+1)]
    cases = 0
    for group in groups:
        for actual in group:
            for bits in product((False, True), repeat=size):
                W = {i for i, value in enumerate(bits) if value}
                truth = tuple(any(i < j for i in W) for j in range(size+1))
                if truth not in actual:
                    continue
                verdict, f, q, v = majority_search(group, actual, W)
                assert verdict == bool(W)
                assert 2**f <= len(group) and q <= 2 * (len(actual) + f) and v <= len(actual)
                cases += 1
    return cases


def game(k, m, oracle_cost, verify_cost):
    # Hidden tuples remain possible on negative inputs even if one of their
    # private points has been verified false. Include all these worlds.
    worlds = [(ws, true_i) for ws in product(range(m), repeat=k)
              for true_i in range(-1, k)]
    def mask(test):
        return sum(1 << j for j, (ws, true_i) in enumerate(worlds) if test(ws, true_i))
    yes = mask(lambda ws, i: i >= 0)
    initial = (1 << len(worlds)) - 1
    cuts = []
    for i in range(k):
        # Asking about the complementary set induces the same binary cut.
        for subset in range(1, 1 << (m-1)):
            cuts.append((mask(lambda ws, t: subset & (1 << ws[i])), oracle_cost))
        for point in range(m):
            cuts.append((mask(lambda ws, t: t == i and ws[i] == point), verify_cost))
    @lru_cache(None)
    def cost(alive):
        if not (alive & yes) or not (alive & ~yes):
            return 0
        options = (price + max(cost(alive & split), cost(alive & ~split))
                   for split, price in cuts if alive & split and alive & ~split)
        return min(options)
    expected = k * min(oracle_cost*a + verify_cost*((m+(1 << a)-1) >> a)
                       for a in range((m-1).bit_length()+1))
    assert cost(initial) == expected
    return len(worlds)


def strict_comparator(bits, upper):
    # All input variables are 1..bits. Gate variables and pads are fresh.
    following = bits + 1
    clauses = [(following,)]
    for i in range(bits, 0, -1):
        z = bits + 2 + bits - i
        a, b = -i, following
        is_or = (upper >> (bits-i)) & 1
        if is_or:
            clauses.extend([(-a, z), (-b, z), (a, b, -z)])
        else:
            clauses.extend([(a, -z), (b, -z), (-a, -b, z)])
        following = z
    clauses.append((following,))
    p, q = 2*bits + 2, 2*bits + 3
    strict = []
    for c in clauses:
        if len(c) == 1:
            strict.extend(c + (a, b) for a, b in product((p, -p), (q, -q)))
        elif len(c) == 2:
            strict.extend((c+(p,), c+(-p,)))
        else:
            strict.append(c)
    assert all(len(c) == 3 and len(set(map(abs, c))) == 3 for c in strict)
    return strict, q


def check_comparators():
    count = 0
    for bits in (1, 2, 3):
        for upper in range(1 << bits):
            cnf, maximum = strict_comparator(bits, upper)
            seen = set()
            for model in product((0, 1), repeat=maximum):
                if all(any(model[abs(x)-1] == (x > 0) for x in c) for c in cnf):
                    value = sum(model[i] << (bits-i-1) for i in range(bits))
                    seen.add(value)
            assert seen == set(range(upper+1))
            count += 1
    return count


if __name__ == '__main__':
    tables = check_joint_models()
    prices = list(product((1, 2, 5), (1, 3)))
    games = sum(bool(game(k, m, a, b)) for k, m in ((1, 5), (2, 2), (2, 3), (2, 4))
                for a, b in prices)
    print(f'{tables} truthful-row cases with fallible peers, {games} exact minimax games, '
          f'{check_comparators()} proper comparator CNFs')
