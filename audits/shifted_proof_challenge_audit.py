"""Finite checks for translated batch scores and a public address sampler."""

from collections import Counter
from itertools import combinations, permutations, product
from math import comb


def translated_scores():
    alphabet = range(4)
    checked = 0
    for size in range(1, 5):
        for batch in product(alphabet, repeat=size):
            for predicate in product((0, 1), repeat=len(alphabet)):
                scores = [sum(predicate[r ^ shift] for r in batch) for shift in alphabet]
                assert sum(scores) == size * sum(predicate)
                assert max(scores) * len(alphabet) >= size * sum(predicate)
                checked += 1
    return checked


# Slots 0 and 1 address the proof, 2 and 3 address the public input.
def trees(depth):
    if not depth:
        return [False, True]
    smaller = trees(depth - 1)
    return [False, True] + list(product(range(4), smaller, smaller))


def run(tree, values, simulated_tape=None):
    trace = []
    while not isinstance(tree, bool):
        address, zero, one = tree
        answer = (values[address] if simulated_tape is None
                  else simulated_tape[len(trace)])
        trace.append(address)
        tree = one if answer else zero
    return tree, trace


def public_address(tree, slot, simulated_tape):
    _, trace = run(tree, None, simulated_tape)
    if slot < len(trace) and trace[slot] < 2:
        return trace[slot]
    return 0


def audit_sampler():
    q = 2
    two_bits = list(product((0, 1), repeat=q))
    candidates = trees(q)
    accepting_pairs = 0
    # A single tree and a second tree selected by a public pairing provide two
    # possible fresh challenges. Every depth-two Boolean tree is tried first.
    for index, first in enumerate(candidates):
        second = candidates[(337 * index + 89) % len(candidates)]
        verifier = (first, second)
        counts = Counter(public_address(tree, slot, tape)
                         for tree in verifier for slot in range(q) for tape in two_bits)
        for raw in two_bits:
            scores = {proof: sum(run(tree, proof + raw)[0] for tree in verifier)
                      for proof in two_bits}
            for proof, score in scores.items():
                if score != len(verifier):
                    continue
                for decoded, new_score in scores.items():
                    if new_score == len(verifier):
                        continue
                    disagreement = sum(count for addr, count in counts.items()
                                       if proof[addr] != decoded[addr])
                    # Counts are out of |coins| * Q * 2^Q. Every rejecting coin
                    # contributes at least one shadowing tape and one bad slot.
                    assert disagreement >= len(verifier) - new_score
                    accepting_pairs += 1
    assert accepting_pairs > 0
    return len(candidates), accepting_pairs


def audit_target_exposure():
    size = 6
    probes_per_target = 2  # One forward probe and one to validate the answer.
    targets_per_batch = 2
    cap = targets_per_batch * probes_per_target
    permutation_list = list(permutations(range(size)))
    checked = 0
    for targets in permutations(range(size), targets_per_batch):
        for program in range(3):
            full_success = 0
            containment = 0
            for perm in permutation_list:
                seen = set()
                passed = True
                for target in targets:
                    seen.add(target)
                    candidate = (perm[target] + program * target) % size
                    seen.add(candidate)
                    passed = passed and perm[candidate] == target
                for address in range(size):
                    if len(seen) == cap:
                        break
                    seen.add(address)
                exposed_values = {perm[address] for address in seen}
                covered = all(target in exposed_values for target in targets)
                assert not passed or covered
                full_success += passed
                containment += covered
            # Equality holds for any adaptive reveal schedule padded to `cap`.
            assert containment * comb(size, targets_per_batch) == (
                len(permutation_list) * comb(cap, targets_per_batch))
            assert full_success <= containment
            checked += 1
    return checked


def audit_partial_completion():
    cells = range(3)
    inputs = list(product((0, 1), repeat=len(cells)))
    cylinders = [tuple(zip(indices, bits)) for size in range(3)
                 for indices in combinations(cells, size)
                 for bits in product((0, 1), repeat=size)]
    families = [family for count in range(3) for family in combinations(cylinders, count)]

    def matches(observations, cylinder):
        return all(i not in observations or observations[i] == bit for i, bit in cylinder)

    def accepts(family, array):
        return any(all(array[i] == bit for i, bit in cylinder) for cylinder in family)

    masks = {family: {a for a in inputs if accepts(family, a)} for family in families}
    checked = 0
    for zero, one in product(families, repeat=2):
        if masks[zero] & masks[one]:
            continue
        h0 = max(map(len, zero), default=0)
        h1 = max(map(len, one), default=0)
        for array in inputs:
            seen = {}
            for _ in range(h1):
                chosen = next((c for c in zero if matches(seen, c)), None)
                if chosen is None:
                    output = 1
                    break
                seen.update((i, array[i]) for i, _ in chosen)
                if matches(seen, chosen):
                    output = 0
                    break
            else:
                output = int(any(matches(seen, c) for c in one))
            assert len(seen) <= h0 * h1
            assert array not in (masks[one] if output == 0 else masks[zero])
            checked += 1
    return checked


if __name__ == '__main__':
    ntrees, pairs = audit_sampler()
    print(f'{translated_scores()} batch/predicate pairs passed translation averaging')
    print(f'{ntrees} adaptive verifier pairs, {pairs} honest/decoded disagreements audited')
    print(f'{audit_target_exposure()} adaptive preimage-validation schedules checked on all 6! permutations')
    print(f'{audit_partial_completion()} three-bit partial certificate completions checked')
