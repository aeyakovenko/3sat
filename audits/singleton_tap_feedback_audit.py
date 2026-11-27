"""Compare sparse progression endpoint prediction with serial homogeneous feedback."""
from itertools import combinations

def single_tap(a, other, seeds, horizon):
    """Compute the output at horizon without allocating a delay-length buffer."""
    other = set(other)
    seeds = set(seeds)
    if a <= 0 or horizon < 0 or any(b <= 0 for b in other) or any(s >= 0 for s in seeds):
        raise ValueError("taps must be positive, seeds negative and horizon nonnegative")

    # ends[r] is the last admissible tick on residue r. Until a genuine death
    # has been found, the provisional progression survives up to the horizon.
    ends = {s + a: horizon for s in seeds if -a <= s}
    live = {r for r in ends if r <= horizon}
    now = 0
    while live:
        earliest = horizon + 1
        killed = None
        for r in live:
            lower = max(0, (now - r + a - 1) // a)
            upper = (horizon - r) // a
            if lower > upper:
                continue
            # Changes to parity are stored at inclusive start and exclusive end.
            events = {lower: 0, upper + 1: 0}

            def add_interval(first, last):
                first = max(first, lower)
                last = min(last, upper)
                if first <= last:
                    events[first] = events.get(first, 0) ^ 1
                    events[last + 1] = events.get(last + 1, 0) ^ 1

            for b in other:
                parent = (r - b) % a
                if parent in ends:
                    offset = (b + parent - r) // a
                    add_interval(offset, offset + (ends[parent] - parent) // a)
                for seed in seeds:
                    t = b + seed
                    if (t - r) % a == 0:
                        j = (t - r) // a
                        add_interval(j, j)
            parity = 0
            for j in sorted(events):
                parity ^= events[j]
                if j <= upper and not parity:
                    t = r + a*j
                    if t < earliest:
                        earliest, killed = t, r
                    break
        if killed is None:
            break
        ends[killed] = earliest - a
        live.remove(killed)
        now = earliest + 1
    residue = horizon % a
    return int(residue in ends and horizon <= ends[residue])


def direct(a, other, seeds, horizon):
    history=set(seeds)
    for t in range(horizon+1):
        if t-a in history and sum(t-b in history for b in other)%2:
            history.add(t)
    return int(horizon in history)

if __name__=='__main__':
    checks=0
    for a in range(1,6):
        for k in range(1,4):
            for other in combinations(range(1,6),k):
                for m in range(4):
                    for seed in combinations(range(-6,0),m):
                        for horizon in (0,1,4,9,25,71):
                            assert single_tap(a,other,seed,horizon)==direct(a,other,seed,horizon)
                            checks+=1
    # An extremely long tap kills a previously all-one chain exactly when
    # it first reaches a seed. Neither a physical sweep nor a D-word buffer
    # fits these parameters.
    gap = (1 << 3000) + 25
    for t, expected in [(gap-3,1), (gap-2,0), (gap-1,0), (1 << 6000,0)]:
        assert single_tap(1, (2,gap), (-2,-1), t) == expected

    # A growing singleton lag also allows two live chains when the supplied
    # earlier seeds depend on that lag. Each progression supports the other.
    step = (1 << 3701) + 19
    seeds = (2-step, 7-step)
    for offset in (0,2,3,7):
        t = ((1 << 2901)+3)*step + offset
        assert single_tap(step, (step-5,step+5), seeds, t) == int(offset in (2,7))

    # Replace a long polynomial sample time with a known stabilized point
    # on precisely the same residue class avoiding a large-power computation.
    sampled = 0
    for width in range(7,31):
        a = 3
        other = (2, 9*width-7)
        seeds = (-6,-2,-1)
        cap = (len(seeds)+1)*(max(a,*other) + a)
        horizon = 14*width**5 + 8
        congruent = cap + ((14*pow(width,5,a)+8-cap) % a)
        assert horizon >= cap
        assert single_tap(a,other,seeds,horizon) == single_tap(a,other,seeds,congruent)
        sampled += 1
    print(f'{checks} exact trajectory endpoints, 8 several-thousand-bit queries, '
          f'{sampled} periodic reductions of the sampling time')
