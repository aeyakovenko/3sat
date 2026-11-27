"""Finite check of anchor-row extension and small witnesses of unrelatedness."""

from itertools import combinations, product
from random import Random


def span(rows):
    result = {0}
    for row in rows:
        result |= {value ^ row for value in result}
    return result


def related(rows, columns, cap):
    coeff_span = span(row >> 1 for row in rows)
    for tag in range(1 << columns):
        if all(((tag & (row >> 1)).bit_count() & 1) == (row & 1) for row in rows):
            return len(coeff_span) <= 1 << cap
    return False


def boxes_for_anchors(rows, cap):
    """A row encodes (coefficient bits, right side in the least bit)."""
    cells = len(rows)
    boxes = set()
    for r in range(cap + 1):
        for chosen in combinations(range(cells), r):
            for values in product(range(4), repeat=r):
                anchors = [rows[a][v] for a, v in zip(chosen, values)]
                if len(span(row >> 1 for row in anchors)) != 1 << r:
                    continue
                row_space = span(anchors)
                pinned = dict(zip(chosen, values))
                box = tuple(
                    tuple(v for v in range(4) if rows[a][v] in row_space
                          and (a not in pinned or pinned[a] == v))
                    for a in range(cells)
                )
                if all(box):
                    boxes.add(box)
    return boxes


def check_template(rows, columns, cap):
    cells = len(rows)
    boxes = boxes_for_anchors(rows, cap)
    all_states = list(product(range(4), repeat=cells))
    true_states = {s for s in all_states if related(
        [rows[a][v] for a, v in enumerate(s)], columns, cap)}
    reconstructed = {s for box in boxes for s in product(*box)}
    assert reconstructed == true_states
    bad = 0
    tight = 0
    for state in all_states:
        if state in true_states:
            continue
        rws = [rows[a][v] for a, v in enumerate(state)]
        smallest = next(k for k in range(1, len(rws) + 1)
                        if any(not related(sub, columns, cap)
                               for sub in combinations(rws, k)))
        assert smallest <= cap + 1
        bad += 1
        tight += smallest == cap + 1

    # -1 stands for a pair whose words have not been pinned.
    pin_masks = {}
    for pin in product(range(-1, 4), repeat=cells):
        mask = sum(1 << a for a, p in enumerate(pin) if p != -1)
        fixed = tuple(v for v in pin if v != -1)
        if mask not in pin_masks:
            pin_masks[mask] = {tuple(v for a, v in enumerate(s) if mask >> a & 1)
                               for s in true_states}
        exists = fixed in pin_masks[mask]
        by_box = any(all(p == -1 or p in allowed for p, allowed in zip(pin, box))
                     for box in boxes)
        assert exists == by_box
    return len(all_states), bad, tight, 5 ** cells


def main():
    rng = Random(49)
    totals = [0, 0, 0, 0]
    tested = 0
    for cells, columns in [(3, 2), (4, 3)]:
        # Each aligned pair has four binary word pairs. Include repeated
        # coefficient rows, inconsistent right sides, and rank deficiencies.
        for _ in range(20):
            rows = [[rng.randrange(1 << (columns + 1)) for _ in range(4)]
                    for _ in range(cells)]
            for cap in range(columns + 1):
                counts = check_template(rows, columns, cap)
                totals = [left + right for left, right in zip(totals, counts)]
                tested += 1
    print(f"{tested} templates and rank caps, {totals[0]} memory pairs, "
          f"{totals[1]} unrelated pairs, {totals[2]} tight sparse witnesses, "
          f"{totals[3]} partial-memory extensions")


if __name__ == "__main__":
    main()
