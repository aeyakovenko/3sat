"""All sound schedules until the positive tag wins, with arbitrarily interleaved ranks."""

from functools import lru_cache
from itertools import permutations


def ranks(mask):
    return (i for i in range(mask.bit_length()) if mask & (1 << i))


@lru_cache(maxsize=None)
def schedule_outcomes(pool, outside, pending=None):
    """Return all pairs (nonempty normal searches, final live pool mask)."""
    if pending is not None:
        # A genuine win by the pending responder would falsify the exclusion.
        # On this follow-up only outsiders strictly earlier than it can win.
        return frozenset(
            outcome
            for win in ranks(outside) if win < pending
            for outcome in schedule_outcomes(pool, outside ^ (1 << win))
        )

    # If the selected pair is absent, either the tag wins, or any outsider can.
    outcomes = {(0, pool)}
    for win in ranks(outside):
        outcomes.update(schedule_outcomes(pool, outside ^ (1 << win)))

    for first, second in permutations(ranks(pool), 2):
        for a, survivors in schedule_outcomes(pool ^ (1 << first), outside, second):
            outcomes.add((a + 1, survivors))
        for win in ranks(outside):
            if win < first:
                for a, survivors in schedule_outcomes(pool, outside ^ (1 << win)):
                    outcomes.add((a + 1, survivors))
    return frozenset(outcomes)


@lru_cache(maxsize=None)
def max_matching_touching(live, exceptional):
    """Largest matching allowed by the absence of every pool/pool exclusion."""
    if not live:
        return 0
    first = live & -live
    rest = live ^ first
    best = max_matching_touching(rest, exceptional & rest)
    for i in ranks(rest):
        second = 1 << i
        if exceptional & (first | second):
            remaining = rest ^ second
            best = max(best, 1 + max_matching_touching(remaining, exceptional & remaining))
    return best


def cooldown_layout(layout):
    tag = len(layout)
    role_mask = {role: sum(1 << i for i, member in enumerate(layout) if member == role)
                 for role in 'PRGCS'}
    pool, raw, guards, suppliers = (role_mask[role] for role in 'PRGS')
    responder = layout.index('C') if 'C' in layout else None
    if responder is not None:
        assert suppliers.bit_count() > responder and min(ranks(suppliers)) > responder
    # All remaining pool members, guards and raw ranks can win zero after this
    # finite prefix. Thus even treating every surviving raw as honest is valid.
    states = [((1 << tag) - 1, None, False, False, 0)]
    seen = set()
    cooldown_winners = set()
    qualifying = 0
    while states:
        state = states.pop()
        if state in seen:
            continue
        seen.add(state)
        live, pending, cooldown, supply_due, elapsed = state
        assert elapsed <= tag + raw.bit_count() and not (cooldown and pending is not None)
        assert guards & live == guards
        choices = [None]
        if pending is None and not cooldown:
            choices.extend(permutations(ranks(pool & live), 2))
        for pair in choices:
            required = list(ranks(suppliers & live))
            if supply_due and responder is not None and live & (1 << responder):
                required.append(responder)
            if not cooldown:
                required.append(tag)
            if pending is not None:
                required.append(pending)
            if pair is not None:
                required.append(pair[0])
            # tag+1 represents a default or any winner above the relevant prefix.
            priority = min(required, default=tag+1)
            winners = [priority, *(r for r in ranks(raw & live) if r < priority)]
            for win in winners:
                if win == pending:
                    continue  # Unsound selected consecutive event.
                if cooldown:
                    who = layout[win] if win < tag else 'default'
                    assert who not in ('P', 'G') and win != tag
                    cooldown_winners.add(who)
                if win == tag:
                    assert not cooldown and pending is None and pair is None
                    assert live & (suppliers | role_mask['C']) == 0
                    exceptional = (live & raw) | guards
                    assert live == exceptional | (live & pool)
                    peers = list(ranks(live & pool))
                    if live.bit_count() * 2 >= tag and len(peers) >= exceptional.bit_count():
                        assert max_matching_touching(live, exceptional) == exceptional.bit_count()
                        matching = list(zip(ranks(exceptional), peers))
                        assert len({v for edge in matching for v in edge}) == 2*exceptional.bit_count()
                        assert all(layout[u] in 'RG' and layout[v] == 'P' for u, v in matching)
                        qualifying += 1
                    continue
                assert win == tag+1 or live & (1 << win)
                following = pair[1] if pair is not None and win == pair[0] else None
                states.append((live & ~(1 << win), following, bool(raw & (1 << win)),
                               bool(suppliers & (1 << win)), elapsed+1))
    return len(seen), qualifying, cooldown_winners


def main():
    layouts = 0
    for size in range(9):
        for pool in range(1 << size):
            outside = ((1 << size) - 1) ^ pool
            p = pool.bit_count()
            available = sum(i < pool.bit_length() - 1 for i in ranks(outside)) if p >= 2 else 0
            expected = set()
            for survivors in range(pool + 1):
                if survivors & ~pool:
                    continue
                lost = p - survivors.bit_count()
                if lost and not any(i < survivors.bit_length() - 1 for i in ranks(outside)):
                    continue
                expected.update((a, survivors) for a in range(lost, available + 1))
            actual = schedule_outcomes(pool, outside)
            assert actual == expected, (size, pool, actual ^ expected)
            counts = {(a, p - survivors.bit_count()) for a, survivors in actual}
            assert counts == {(a, l) for a in range(available + 1) for l in range(min(a, max(0, p-1)) + 1)}
            layouts += 1
    print(f"Verified all {layouts} ranked pool/outsider layouts through eight ranks and every attainable search count and survivor set.")

    # Vary the raw priority positions and include complete control reservoirs.
    small = {''.join(roles) for roles in permutations('RRPGPP')}
    small.update(('RCSSGPPPP', 'RRCSSSGPPPPPP', 'RGPP', 'GPPP'))
    cooldown_types = set()
    state_count = qualifying = 0
    for layout in sorted(small):
        reached, matched, types = cooldown_layout(layout)
        state_count += reached
        qualifying += matched
        cooldown_types.update(types)
    assert {'R', 'S', 'default'} <= cooldown_types and qualifying > 0
    print(f"Verified cooldown, tag deadline and matching checks on {len(small)} layouts, "
          f"{state_count} reachable states, and {qualifying} qualifying tag states with enough partners.")


if __name__ == '__main__':
    main()
