"""Check signed-subtotal descent, sparse moments, and full assignments on printed CNFs."""

from itertools import product
from random import Random

from offline_weighted_dominance_audit import Grid
from weighted_range_transcript_audit import Transcript, parse


IDS = (1, 2, 3, 5, 6)
QUERIES = ((5, 6), (1, 4), (7, 7), (2, 7), (3, 2))
UPDATES = ((0, 1, 1, 2), (4, 3, 2, 3))


def transposed_total(indices):
    retained = [(IDS[i], *QUERIES[i]) for i in reversed(indices)]
    grid = Grid([(7 - x, 7 - y) for _, x, y in retained], 3, 2)
    return sum(w * grid.count(7 - x, 7 - y, sum(j > t for j, _, _ in retained))
               for t, x, y, w in UPDATES)


def subsets():
    return [tuple(i for i in range(len(IDS)) if mask >> i & 1)
            for mask in range(1 << len(IDS))]


def recover(indices, signs, subtotal, raw_error):
    def evaluate(group):
        return sum(sign * raw_error(tuple(i for i in group if signs[i] == sign))
                   for sign in (-1, 1))

    assert subtotal
    while len(indices) > 1:
        middle = len(indices) // 2
        left, right = indices[:middle], indices[middle:]
        delta = evaluate(left)
        if delta:
            indices, subtotal = left, delta
        else:
            indices = right
    assert subtotal == signs[indices[0]] * raw_error(indices)
    return indices[0]


def check_printed_model(builder, claims, chosen):
    records = []
    for t, x, y, w in UPDATES:
        for field, value in enumerate((x, y, w)):
            records.extend(('U', t, field, bit, value >> bit & 1)
                           for bit in range(builder.bits))
    for j, (x, y), claim in zip(IDS, QUERIES, claims):
        records.extend((('Q', j, x, y), ('A', j, claim)))
    slots = list(range(len(builder.receipts)))
    Random(983).shuffle(slots)
    rows, size = parse(builder.file(records, slots))
    # Supply only the selected query and pinned anchors. The finite check uses
    # unit propagation to reconstruct the remaining wires independently of the proof.
    assigned = {1: False, 2: False, 3: False}
    assigned.update({v: j == chosen for j, v in builder.query.items()})
    while len(assigned) < size:
        old_size = len(assigned)
        for row in rows:
            if any(abs(lit) in assigned and assigned[abs(lit)] == (lit > 0) for lit in row):
                continue
            unknown = [lit for lit in row if abs(lit) not in assigned]
            assert unknown
            if len(unknown) == 1:
                lit = unknown[0]
                assigned[abs(lit)] = lit > 0
        assert len(assigned) > old_size
    assert all(any(assigned[abs(lit)] == (lit > 0) for lit in row) for row in rows)


def main():
    groups = subsets()
    transposed = {group: transposed_total(group) for group in groups}
    true_words = [transposed[(i,)] for i in range(len(IDS))]
    direct = [sum(w for t, x, y, w in UPDATES if t < j and x <= a and y <= b)
              for j, (a, b) in zip(IDS, QUERIES)]
    assert true_words == direct
    builder = Transcript(7, 'UQQQUQQ')
    descents = moment_cases = models = 0
    for errors in product((-1, 0, 1), repeat=len(IDS)):
        claims = [word + error for word, error in zip(true_words, errors)]
        raw = {group: sum(claims[i] for i in group) - transposed[group] for group in groups}
        selected = set()
        for signs in product((-1, 0, 1), repeat=len(IDS)):
            group = tuple(i for i, sign in enumerate(signs) if sign)
            subtotal = sum(sign * raw[tuple(i for i in group if signs[i] == sign)]
                           for sign in (-1, 1))
            if subtotal:
                i = recover(group, signs, subtotal, raw.__getitem__)
                assert errors[i]
                selected.add(i)
                descents += 1
        for k in (1, 2, 3):
            for allowed in groups:
                if not 1 <= sum(errors[i] != 0 for i in allowed) <= k:
                    continue
                masks = (tuple(i for i in allowed if (IDS[i] ** r) >> bit & 1)
                         for r in range(k) for bit in range((max(IDS) ** r).bit_length()))
                assert any(raw[mask] for mask in masks)
                moment_cases += 1
        if selected:
            check_printed_model(builder, claims, IDS[min(selected)])
            models += 1
    print(f"{descents} nonzero signed descents, {moment_cases} sparse candidate sets, "
          f"{models} full checked DIMACS assignments")


if __name__ == '__main__':
    main()
