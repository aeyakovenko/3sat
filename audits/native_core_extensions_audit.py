"""Check the exact-width switch gadget using all 256 clause subsets on three bank bits."""

from itertools import product


def forbidding_clause(names, values):
    return tuple(-name if value else name for name, value in zip(names, values))


def satisfied(clause, values):
    return any(values[abs(literal) - 1] == (literal > 0) for literal in clause)


def models(clauses):
    return [
        values
        for values in product((False, True), repeat=7)
        if all(satisfied(clause, values) for clause in clauses)
    ]


def main():
    reserve = (1, 2, 3)
    switch = 4
    bank = (5, 6, 7)
    anchors = [
        forbidding_clause(reserve, bits)
        for bits in product((False, True), repeat=3)
        if any(bits)
    ]
    guards = [(switch, -name, reserve[0]) for name in bank]
    template = anchors + guards
    negative_pin = (-switch, reserve[0], reserve[1])
    positive_pin = (switch, reserve[0], reserve[1])
    clauses = [forbidding_clause(bank, bits) for bits in product((False, True), repeat=3)]
    assert all(len(set(map(abs, clause))) == 3 for clause in template + clauses + [negative_pin, positive_pin])

    intact = models(template + [negative_pin])
    flipped = models(template + [positive_pin])
    deleted = models(template)
    assert len(intact) == 1 and len(flipped) == 8 and len(deleted) == 9
    changed = 0
    for mask in range(1 << len(clauses)):
        extra = [clause for index, clause in enumerate(clauses) if mask & (1 << index)]
        sat = mask != (1 << len(clauses)) - 1
        zero = not (mask & 1)
        answers = [any(all(satisfied(c, v) for c in extra) for v in case) for case in (intact, flipped, deleted)]
        assert answers == [zero, sat, sat]
        changed += zero != sat
    print(f"Verified 256 exact-width extensions. The single sign flip changes {changed} verdicts.")


if __name__ == "__main__":
    main()
