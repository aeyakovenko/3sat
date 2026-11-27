"""Exhaust sign edits at labeled cubic vertices using exact assignment bitsets."""
from itertools import combinations, product
from math import comb


def census(edges, max_edits, check_deletions=False):
    edges = sorted(tuple(sorted(edge)) for edge in edges)
    sites = sorted({v for edge in edges for v in edge})
    assignments = 1 << len(edges)
    universe = (1 << assignments) - 1
    candidate_masks = []
    blockers = []
    all_options = []
    for v in sites:
        incident = sorted((b if a == v else a, i) for i, (a, b) in enumerate(edges) if v in (a, b))
        assert len(incident) == 3
        masks = [0] * 8
        for x in range(assignments):
            pattern = sum(((x >> i) & 1) << j for j, (_, i) in enumerate(incident))
            masks[pattern] |= 1 << x
        blockers.append(masks)
        original = [b for b in range(8) if b.bit_count() % 2 != int(v == 0)]
        options = [(None, original)]
        for b in original:
            for digit in range(3):
                a = b ^ (1 << digit)
                options.append(((b, a), [a if x == b else x for x in original]))
        all_options.append(options)
        candidate_masks.append([universe ^ sum(masks[p] for p in forbidden)
                                for _, forbidden in options])

    result = []
    critical = 0
    first = None
    for k in range(max_edits + 1):
        total = unsat = 0
        for selected in combinations(sites, k):
            for choices in product(range(1, 13), repeat=k):
                ids = [0] * len(sites)
                for v, choice in zip(selected, choices):
                    ids[v] = choice
                solutions = universe
                for v in sites:
                    solutions &= candidate_masks[v][ids[v]]
                total += 1
                if solutions:
                    continue
                unsat += 1
                if not k or not check_deletions:
                    continue
                rows = [(v, p) for v in sites for p in all_options[v][ids[v]][1]]
                for omit in range(len(rows)):
                    kept = universe
                    for j, (v, p) in enumerate(rows):
                        if j != omit:
                            kept &= ~blockers[v][p]
                    assert kept
                    critical += 1
                if first is None:
                    reversions = []
                    for omit in sites:
                        kept = universe
                        for v in sites:
                            kept &= candidate_masks[v][0 if v == omit else ids[v]]
                        reversions.append((kept.bit_count(), (kept & -kept).bit_length() - 1))
                    first = [all_options[v][ids[v]][0] for v in sites], reversions
        assert total == comb(len(sites), k) * 12**k
        result.append((total, unsat))
    return result, critical, first


def main():
    k4 = list(combinations(range(4), 2))
    result, deleted, witness = census(k4, 4, True)
    assert result == [(1, 1), (48, 0), (864, 0), (6912, 0), (20736, 96)]
    assert deleted == 1536
    assert witness == ([(0, 1), (1, 0), (4, 5), (4, 6)], [(3, 1), (3, 0), (1, 39), (1, 56)])
    print("K4 (total, UNSAT) at 0..4 edits:", result)
    print("Satisfiable single-clause deletions across all 96 four-edit UNSAT cases:", deleted)
    print("First (re-admitted, withdrawn) tuples and single-edit reversions:", witness)
    prism = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5)]
    k33 = [(u, v) for u in range(3) for v in range(3, 6)]
    for name, graph in (("prism", prism), ("K3,3", k33)):
        result, _, _ = census(graph, 4)
        assert result == [(1, 1), (72, 0), (2160, 0), (34560, 0), (311040, 0)]
        print(name, "(total, UNSAT) at 0..4 edits:", result)


if __name__ == "__main__":
    main()
