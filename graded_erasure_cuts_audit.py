"""Exhaust erasure matchings, public suffix predictions and variable-cut transcripts."""

from collections import Counter
from itertools import combinations, product
from math import ceil, comb, log


def restriction(word, positions):
    return tuple(word[i] for i in positions)


def outside(holes, m):
    return tuple(i for i in range(m) if i not in holes)


def projection_matching(words, holes):
    """A partial word is represented by (its erased positions, its retained symbols)."""
    complements = {h: outside(h, len(words[0])) for h in holes}
    neighborhood = {
        a: [(h, restriction(a, complements[h])) for h in holes] for a in words
    }
    owner = {}

    def augment(a, used):
        for erased in neighborhood[a]:
            if erased in used:
                continue
            used.add(erased)
            if erased not in owner or augment(owner[erased], used):
                owner[erased] = a
                return True
        return False

    for a in words:
        augment(a, set())
    return owner


def prediction_cover(words, holes):
    """Each pass chooses one prediction per hole set for each still-uncovered row."""
    full_rows = set(words)
    remaining = set(words)
    assignments = {}
    tables = []
    while remaining:
        table = {}
        for h in holes:
            if not remaining:
                break
            counts = Counter(restriction(a, h) for a in remaining)
            prediction = min(counts, key=lambda value: (-counts[value], value))
            table[h] = prediction
            covered = {a for a in remaining if restriction(a, h) == prediction}
            assert len(covered) == counts[prediction]
            for a in covered:
                assignments[a] = (len(tables), h)
            remaining -= covered
        tables.append(table)
    assert set(assignments) == full_rows
    return tables, assignments


def check_roster_encodings(words, k):
    """Pick a different candidate cut for each row; full address/value logs identify rows."""
    m = len(words[0])
    descriptions = {}
    for db in words:
        rank = sum(v * k**i for i, v in enumerate(db))
        j = 1 + rank % m
        # Let unrestricted preprocessing choose the disclosure order using the WHOLE row.
        order = sorted(range(m), key=lambda i: ((db[i] + rank*i) % k, i))
        h = tuple(sorted(order[:j]))
        visible = outside(h, m)
        digits = 0
        for i in visible:
            digits = k*digits + db[i]
        assert digits < k**(m-j)
        tag = rank % m
        program = rank % 3
        search_order = h if program == 0 else tuple(reversed(h))
        log_entries = tuple((i, db[i]) for i in search_order)
        # Transcript contains only probes into data at the holes, not an input x field.
        description = (tag, program, j, h, digits, log_entries)
        assert description not in descriptions
        descriptions[description] = db
    return len(descriptions)


def audit():
    cross_queries = matching_checks = covering_checks = roster_encodings = 0
    for k, max_m in ((2, 6), (3, 4), (4, 3)):
        for m in range(1, max_m + 1):
            words = list(product(range(k), repeat=m))
            roster_encodings += check_roster_encodings(words, k)
            for j in range(1, m + 1):
                holes = list(combinations(range(m), j))
                decoder = projection_matching(words, holes)
                # Biregularity saturates the smaller side, in both degree regimes.
                assert len(decoder) == min(k**m, comb(m,j) * k**(m-j))
                assert (len(decoder) == len(words)) == (comb(m,j) >= k**j)
                for (h, frozen), a in decoder.items():
                    assert restriction(a, outside(h, m)) == frozen
                matching_checks += 1

                tables, assignments = prediction_cover(words, holes)
                passes = max(1, ceil((1 + m*log(k))*k**j / comb(m,j)))
                assert len(tables) <= passes
                for a in words:
                    seed, h = assignments[a]
                    prediction = tables[seed][h]
                    visible = outside(h, m)
                    for x in words:
                        # One bit from an earlier full comparison, plus H, s, and x_H.
                        # This step cannot inspect x at the frozen sites again.
                        flag = restriction(a, visible) == restriction(x, visible)
                        answer = flag and restriction(x, h) == prediction
                        assert answer == (a == x)
                        cross_queries += 1
                covering_checks += 1
    print(f'{matching_checks} exact matching thresholds; {covering_checks} greedy covers; '
          f'{cross_queries:,} suffix equality queries with a one-bit prefix flag; '
          f'{roster_encodings} variable-cut descriptions checked.')


if __name__ == '__main__':
    audit()
