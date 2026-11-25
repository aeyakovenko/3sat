"""Construct an explicit finite test set defeating all six-step binary-branch RAMs."""

from itertools import combinations_with_replacement, product
from two_load_five_slot_audit import OPS, signed

BASE = (4, 4, 8, 8)
NEGATIVE_CODES = "DD77 8EB6 F488 4F88 44F8 448F".split()


def comparison_agreements(a, b):
    # Bit i says negative example i has the same branch result as the base.
    unsigned = [(x > y) - (x < y) for x, y in zip(a, b)]
    signed_order = [(signed(x) > signed(y)) - (signed(x) < signed(y)) for x, y in zip(a, b)]
    for sequence in (unsigned, signed_order):
        for kind in (-1, 0, 1):
            want = sequence[0] == kind
            yield sum(1 << i for i, relation in enumerate(sequence[1:]) if (relation == kind) == want)


def main():
    negatives = [tuple(int(c, 16) for c in code) for code in NEGATIVE_CODES]
    assert all(all(x >= 4 for x in row) and ((row[0] & row[2]) or (row[1] & row[3]))
               for row in negatives)
    assert not (BASE[0] & BASE[2]) and not (BASE[1] & BASE[3])
    assert all(tuple(15 if j == i else v for j, v in enumerate(BASE)) in negatives
               for i in range(4))
    suite = [BASE] + negatives
    raw = tuple(zip(*suite))
    words = [(c,) * len(suite) for c in range(16)] + list(raw)

    elementary = {agree for a, b in combinations_with_replacement(words, 2)
                  for agree in comparison_agreements(a, b)}
    transcripts = {a & b for a, b in combinations_with_replacement(elementary, 2)}

    alu = {tuple(op(x, y) & 15 for x, y in zip(a, b))
           for op in OPS for a, b in product(words, repeat=2)}
    for q in alu:
        lookup = tuple(row[address] if address < 4 else 0 for row, address in zip(suite, q))
        for a, options in ((q, words), (lookup, words + [q])):
            for b in options:
                transcripts.update(comparison_agreements(a, b))
    assert 0 not in transcripts

    # Confirm the selected negatives hit every base-accepting transcript.
    kept = (1 << len(negatives)) - 1
    for i in range(len(negatives) - 4):
        smaller = kept ^ (1 << i)
        if all(smaller & signature for signature in transcripts):
            kept = smaller
    print(f"{len(alu)} ALU tables, {len(transcripts)} accepting transcript patterns")
    print("Defeating suite: 4488 SAT plus UNSAT inputs",
          " ".join(label for i, label in enumerate(NEGATIVE_CODES) if kept >> i & 1))


if __name__ == '__main__':
    main()
