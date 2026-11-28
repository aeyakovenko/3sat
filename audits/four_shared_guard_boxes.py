#!/usr/bin/env python3
"""Exhaust four disjoint easy boxes with one common dormant guard and three other pins.

A signed integer is a literal known to be true throughout a box. The guard is
implicit. All variables outside the displayed pins are free within each box.
Global renaming and polarity changes normalize the first row. Each further
row must mention an old variable in order to conflict with an earlier row.
The new variables in that row can be renamed consecutively and have their
signs flipped independently, before later rows are selected. Every actual
ordered configuration therefore occurs up to these symmetries; unique orbit
representatives are unnecessary for the universal check.
"""

from itertools import combinations, product


def extensions(previous):
    """Choose old variables with either sign, followed by consecutive, positive fresh names."""
    used = max(abs(literal) for row in previous for literal in row)
    for count in range(1, 4):
        for names in combinations(range(1, used + 1), count):
            for signs in product((1, -1), repeat=count):
                row = tuple(v * s for v, s in zip(names, signs))
                row += tuple(range(used + 1, used + (3 - count) + 1))
                if all(any(-literal in old for literal in row) for old in previous):
                    yield row


def can_designate_changed_name(i, rows):
    """The other boxes must satisfy the edited clause through one of its two shared literals."""
    row = rows[i]
    return any(all(j == i or any(-p in other for p in row if p != changed)
                   for j, other in enumerate(rows)) for changed in row)


def clause_supports(rows):
    """One chosen true pin per box must fit in a single nontautological width-three clause."""
    supports = set()
    for hits in product(*rows):
        literals = set(hits)
        if len(literals) <= 3 and all(-p not in literals for p in literals):
            supports.add(frozenset(abs(p) for p in literals))
    return supports


def meeting_pair(rows):
    variables = sorted({abs(p) for row in rows for p in row})
    supports = clause_supports(rows)
    for a, b in combinations(variables, 2):
        if all(a in support or b in support for support in supports):
            return a, b
    return None


def main():
    all_types = admitted = no_pair = no_pair_without_edit_roles = 0
    exceptions_with_short_clause = fifth_extensions = fifth_without_pair = 0
    first = (1, 2, 3)
    for second in extensions([first]):
        for third in extensions([first, second]):
            for fourth in extensions([first, second, third]):
                rows = [first, second, third, fourth]
                all_types += 1
                no_witness = meeting_pair(rows) is None
                no_pair_without_edit_roles += no_witness
                if no_witness:
                    exceptions_with_short_clause += any(len(s) <= 2 for s in clause_supports(rows))
                    # Adding a box only shrinks the family of common clauses.
                    for fifth in extensions(rows):
                        fifth_extensions += 1
                        fifth_without_pair += meeting_pair([*rows, fifth]) is None
                if all(can_designate_changed_name(i, rows) for i in range(4)):
                    admitted += 1
                    no_pair += no_witness
    assert (all_types, admitted, no_pair) == (9039, 4980, 0)
    # The edit condition is used; disjoint boxes alone do admit exceptions.
    assert no_pair_without_edit_roles == 72
    assert (exceptions_with_short_clause, fifth_extensions, fifth_without_pair) == (0, 720, 0)
    print(f"{all_types} normalized disjoint quadruples, {admitted} admit every edit role, "
          f"{no_pair} of those lack a two-variable transversal")
    print(f"Ignoring the edit roles leaves {no_pair_without_edit_roles} exceptions, "
          "all without a common short clause")
    print(f"{fifth_extensions} disjoint fifth extensions of the exceptions, "
          f"{fifth_without_pair} lack a two-variable transversal")


if __name__ == "__main__":
    main()
