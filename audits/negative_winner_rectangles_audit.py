"""Enumerate sound finite schedules, including every possible selected pair."""

from itertools import combinations


def outcomes(layout):
    right = {i for i, role in enumerate(layout) if role == "R"}
    left = {i for i, role in enumerate(layout) if role == "L"}
    outsiders = {i for i, role in enumerate(layout) if role == "."}
    supply = {i for i, role in enumerate(layout) if role == "A"}
    control = layout.index("B") if "B" in layout else None
    tag = len(layout)
    assert len(left) == max(right) + 1
    assert max(right) < min(left)
    if control is not None:
        assert len(supply) > control and min(supply) > control

    # A new pair is a representative of any nonempty set of certified
    # exclusions with this pair chosen as its canonical member.
    initial = (frozenset(range(tag)), None, False)
    work = [initial]
    seen = {initial}
    survivors = set()
    while work:
        live, follow, control_due = work.pop()
        assert right <= live
        choices = [None] + [(f, g) for f in sorted(left & live) for g in sorted(right)]
        for pair in choices:
            required = [tag, *(supply & live)]
            if pair is not None:
                required.append(pair[0])
            if follow is not None:
                required.append(follow)
            if control_due and control in live:
                required.append(control)
            top = min(required)
            # An outside reporter is free either to offer or to idle.
            for win in {top} | {u for u in outsiders & live if u < top}:
                if follow is not None and win == follow:
                    continue  # A successful selected pair contradicts soundness.
                assert win not in right
                if win == tag:
                    assert pair is None
                    assert len(left & live) >= len(right)
                    if control is not None:
                        assert control not in live
                    survivors.add(len(left & live))
                    continue
                if win == control:
                    assert control_due
                next_follow = pair[1] if pair is not None and win == pair[0] else None
                state = (live - {win}, next_follow, win in supply)
                if state not in seen:
                    seen.add(state)
                    work.append(state)
    assert survivors
    return len(seen), survivors


def main():
    visited = cases = 0
    for q in range(5):
        for size in range(1, q + 2):
            for earlier in combinations(range(q), size - 1):
                right = set(earlier) | {q}
                layout = "".join("R" if i in right else "." for i in range(q + 1))
                states, survivors = outcomes(layout + "L" * (q + 1))
                # Every number of survivors permitted by the count is attained.
                assert survivors == set(range(size, q + 2))
                visited += states
                cases += 1

    for layout in ["RLB" + "A" * 3, "BRLLA", ".RBALLAA",
                   "B.RLLLA", "R.BRLLLLAAA"]:
        states, _ = outcomes(layout)
        visited += states
        cases += 1
    print(f"{cases} layouts and {visited} distinct partial schedules checked")
    print("Exact survivor range attained in every unrestricted layout.")
    print("Every control responder won directly after one of its zero suppliers.")


if __name__ == "__main__":
    main()
