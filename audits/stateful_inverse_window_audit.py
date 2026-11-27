"""Enumerate adaptive inverse guesses with free, honest feedback after each guess."""

from collections import Counter, defaultdict
from itertools import permutations, product
from math import comb, factorial


def hypergeom_tail(size, labels, budget, threshold):
    """Numerator over the common denominator comb(size, budget)."""
    return sum(comb(labels, h) * comb(size - labels, budget - h)
               for h in range(threshold, min(labels, budget) + 1)
               if budget - h <= size - labels)


def run(table, labels, strategy, masks, kernels, evidence):
    size = len(table)
    inverse = {value: key for key, value in enumerate(table)}
    designated = set(labels)
    seen = {}
    witness = {}
    charged = forward_fresh = inverse_only = 0
    correct = 0
    histories = []
    base_seen = {}
    state = 1

    def probe(key, step, kind):
        nonlocal charged, forward_fresh
        fresh = key not in seen
        new_hit = fresh and table[key] in designated
        if kernels is not None:
            # These histories include inverse-only disclosures; all unexposed
            # entries of the random permutation remain conditionally uniform.
            bucket = (charged, forward_fresh, len(witness), inverse_only, fresh)
            kernels[bucket][0] += 1
            kernels[bucket][1] += int(new_hit)
        charged += 1
        if fresh:
            forward_fresh += 1
            if new_hit:
                witness[table[key]] = (charged, step, kind)
        seen[key] = table[key]
        return table[key]

    for step, label in enumerate(labels):
        # Auxiliary tests made by the audit are invisible to the base predictor.
        # Thus changing fixed correction masks leaves the base histories unchanged.
        if step == 0 or (strategy in ('repeat', 'state') and step == 1):
            if strategy == 'repeat':
                query = 0
            elif strategy == 'state':
                query = (state + label + next(iter(base_seen), 0)) % size
            else:
                query = (label + 1) % size
            out = probe(query, step, 'base')
            base_seen[out] = query
            state = (3 * state + query + out) % size
        if strategy == 'single':
            raw = base_seen.get(label, (label + 2) % size)
        elif strategy == 'repeat':
            raw = (state + label) % size
        else:
            raw = base_seen.get(label, (state + label + step) % size)
        tag = state % len(masks)
        corrected = raw ^ masks[tag]
        # Out-of-range XORs cannot be correct on the original alphabet. The
        # charged probe still occurs, here at the in-range position zero.
        test_key = corrected if corrected < size else 0
        probe(test_key, step, 'test')
        answer = inverse[label]
        if corrected == answer:
            correct += 1
            index, found_at, kind = witness[label]
            assert index <= charged and found_at <= step
            if found_at < step and evidence is not None:
                evidence['earlier_' + kind] += 1
        if answer not in seen:
            inverse_only += 1
            seen[answer] = label
        base_seen[label] = answer
        histories.append((tag, raw, answer))
        state = (state + answer + 2 * label) % size

    assert len({record[0] for record in witness.values()}) == len(witness)
    assert correct <= len(witness)
    assert len(seen) == forward_fresh + inverse_only
    return charged, correct, len(witness), histories


def check_strategy(size, labels, strategy, masks):
    kernels = defaultdict(lambda: [0, 0])
    successes, hits, evidence = Counter(), Counter(), Counter()
    for table in permutations(range(size)):
        budget, correct, discovered, _ = run(table, labels, strategy, masks, kernels, evidence)
        successes[correct] += 1
        hits[discovered] += 1
    assert budget <= size
    for (charged, fresh_count, discovered, disclosed, fresh), (n, new_hits) in kernels.items():
        if fresh:
            available = size - fresh_count - disclosed
            remaining = len(labels) - discovered - disclosed
            assert remaining >= 0 and available > 0
            assert new_hits * available == n * remaining
            assert new_hits * (size - charged) <= n * (len(labels) - discovered)
        else:
            assert new_hits == 0
    for threshold in range(len(labels) + 1):
        measured = sum(count for k, count in successes.items() if k >= threshold)
        forward_hits = sum(count for k, count in hits.items() if k >= threshold)
        assert measured <= forward_hits
        assert forward_hits * comb(size, budget) <= factorial(size) * hypergeom_tail(
            size, len(labels), budget, threshold)
    return len(kernels), evidence


def check_masks(size, labels, choices):
    # Compare selecting correction masks after seeing the table with the union
    # of events for fixed corrections. The base predictor has one discretionary probe.
    masks = list(choices)
    threshold = len(labels)
    count = 0
    for table in permutations(range(size)):
        expected_history = None
        best = 0
        for correction in masks:
            budget, correct, _, history = run(table, labels, 'lookahead', correction, None, None)
            if expected_history is None:
                expected_history = history
            assert expected_history == history
            assert correct == sum((raw ^ correction[tag]) == true for tag, raw, true in history)
            best = max(best, correct)
        count += best >= threshold
    numerator = len(masks) * hypergeom_tail(size, len(labels), budget, threshold)
    denominator = comb(size, budget)
    assert numerator < denominator  # Check a genuinely nontrivial union bound.
    assert count * denominator <= factorial(size) * numerator
    return count


def main():
    buckets = 0
    evidence = Counter()
    for size, labels in ((6, (3, 1, 4)), (7, (5, 0, 3, 1))):
        for strategy in ('lookahead', 'repeat', 'state'):
            for masks in ((0,), (1, 0)):
                count, traces = check_strategy(size, labels, strategy, masks)
                buckets += count
                evidence.update(traces)
    assert evidence['earlier_base'] and evidence['earlier_test']
    single = sum(run(table, (2,), 'single', (0,), None, None)[1]
                 for table in permutations(range(7)))
    assert single == 2 * factorial(6)
    modal = check_masks(7, (4, 0, 2), [(mask,) for mask in range(8)])
    tagged = check_masks(7, (4, 0, 2), product(range(2), repeat=2))
    print(f'12 exhaustive strategy/size/correction settings; '
          f'{buckets} conditional exposure classes satisfied hypergeometric tail domination. '
          f'All three corrected guesses succeeded on {modal}/5040 modal and '
          f'{tagged}/5040 tagged permutations.')


if __name__ == '__main__':
    main()
