"""Semantic audit of advice removal for all CNFs on one proper triple.

Clause j is the proper ternary clause falsified precisely by assignment j.
The three row functions model the answers on the corresponding semantic
queries. The audit does not simulate the RAM-to-DIMACS compiler.
"""
from itertools import combinations, product


def trial(mode, truthful, tag):
    if mode == "correct":
        return truthful
    if mode == "reversed":
        return not truthful
    if mode == "always_no":
        return False
    if mode == "always_yes":
        return True
    return (tag.bit_count() % 2) == 0


def violated_index(clauses, assignment, row):
    """Follow left-completion queries, then validate the single returned index."""
    depth = len(clauses).bit_length()
    valid = {j for j, clause in enumerate(clauses) if assignment == clause}
    prefix = 0
    for remaining in reversed(range(depth)):
        left = 2 * prefix
        possible = any(j >> remaining == left for j in valid)
        prefix = left if trial(row, possible, left + 17 * remaining) else left + 1
    return prefix if prefix < len(clauses) and clauses[prefix] == assignment else None


def audit():
    modes = ("correct", "reversed", "always_no", "always_yes", "tag_parity")
    row_pairs = tuple(product(modes, repeat=2))
    assignment_trials = 0
    menus_tested = 0
    for mask in range(256):
        clauses = [x for x in range(8) if mask >> x & 1]
        models = [x for x in range(8) if x not in clauses]
        # At the exact census, testing coordinates of the first member of an
        # increasing list of models recovers the least actual model.
        if models:
            selections = tuple(combinations(models, len(models)))
            census_assignment = sum(
                int(any(words[0] >> i & 1 for words in selections)) << i
                for i in range(3)
            )
            assert census_assignment == min(models)
        outcomes = {}
        for selector, bit_row in row_pairs:
            isolated = [x for x in models
                        if not trial(selector, any(y < x for y in models), x)]
            assignment = sum(
                int(trial(bit_row, any(x >> i & 1 for x in isolated), i)) << i
                for i in range(3)
            )
            if models and selector == bit_row == "correct":
                assert isolated == [min(models)] and assignment == min(models)
            verdicts = {k: violated_index(clauses, assignment, k) for k in modes}
            assert (verdicts["correct"] is None) == (assignment in models)
            assert all(j is None or clauses[j] == assignment for j in verdicts.values())
            outcomes[selector, bit_row] = verdicts
            assignment_trials += 1

        # Include a misleading row before the good row at every length.
        for h, g, k in product(modes, repeat=3):
            answer = any(
                all(outcomes[a, b][reader] is None for reader in (k, "correct"))
                for a, b in product((h, "correct"), (g, "correct"))
            )
            assert answer == bool(models)
            menus_tested += 1
    print(f"256 formulas, {assignment_trials} implicit assignments, "
          f"{menus_tested} three-stage menus")


def audit_four_reports():
    for width in range(1, 8):
        for reports in range(width + 1):
            observed = min(2 * reports, width)
            probes = 2 ** (width - observed)
            for secret, side in product(range(2**width), range(2)):
                known = 0
                for step in range(reports):
                    # The requested Boolean predicate uses the counterfactual
                    # side to choose between consecutive bits of the marker.
                    pair = [(secret >> (2 * step + b)) & 1 for b in range(2)]
                    known |= (pair[0] + 2 * pair[1]) << (2 * step)
                candidates = [known + (tail << observed) for tail in range(probes)]
                assert any(z == secret and side == 1 for z in candidates) == bool(side)
    print("four-report upper boundary checked for 1 through 7 hidden bits")


if __name__ == "__main__":
    audit()
    audit_four_reports()
