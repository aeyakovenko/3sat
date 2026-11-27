"""Exhaust the lifetime address errors of LRU plus an exceptional address set."""
from itertools import product


def test_trace(trace, address_count):
    memory = [0] * address_count
    last = {}
    distinct_gaps = [0] * address_count
    seen_reads = []
    edges = set()
    for i, (a, kind) in enumerate(trace):
        if kind == 0 and memory[a]:
            between = {b for b, _ in trace[last[a] + 1:i]}
            assert a not in between
            distinct_gaps[a] = max(distinct_gaps[a], len(between))
            edges.update((a, b) for b in between)
        if kind:
            memory[a] = kind - 1
        else:
            seen_reads.append(memory[a])
        last[a] = i
    index = sum(x >= rank for rank, x in enumerate(sorted(distinct_gaps, reverse=True), 1))
    assert len(edges) >= index**2
    for capacity in range(1, address_count + 1):
        cache = {}
        errors = set()
        k = 0
        for a, kind in trace:
            old = cache.pop(a, 0)
            value = kind - 1 if kind else seen_reads[k]
            if not kind:
                if old != value:
                    errors.add(a)
                k += 1
            cache[a] = value
            if len(cache) > capacity:
                del cache[next(iter(cache))]
        assert errors == {a for a, gap in enumerate(distinct_gaps) if gap >= capacity}
        if index < capacity:
            assert len(errors) < capacity


def full_passes(address_count):
    trace = [(a, k) for k in (2, 0) for a in range(address_count)]
    test_trace(trace, address_count)
    assert test_filtered_trace(trace, address_count)[0] == address_count-1
    for a in range(address_count):
        assert {b for b, _ in trace[a+1:a+address_count]} == set(range(address_count)) - {a}


def check_shared_cut(events, witnesses, h):
    """The cuts count events to their left. Only positive touches compete."""
    if h < 2:
        return
    radius = max(1, h // 4)
    shared = [[] for _ in range(len(events) + 1)]
    gaps = [(a, lo, hi) for a, (degree, lo, hi) in witnesses.items() if degree >= h][:h]
    assert len(gaps) == h
    for a, lo, hi in gaps:
        eligible = 0
        for cut in range(lo+1, hi+1):
            left = {b for b, value in events[lo+1:cut] if value}
            right = {b for b, value in events[cut:hi] if value}
            if min(len(left), len(right)) >= radius:
                shared[cut].append((a, lo, hi))
                eligible += 1
        assert eligible >= h-2*radius+1
    center = max(range(len(shared)), key=lambda i: len(shared[i]))
    assert len(shared[center]) * len(shared) >= h * (h-2*radius+1)
    for cut in range(center-radius//2, center+radius//2+1):
        for a, lo, hi in shared[center]:
            assert lo < cut <= hi and events[lo] == events[hi] and events[lo][1] != 0
            assert all(b != a for b, _ in events[lo+1:hi])
            left = {b for b, value in events[lo+1:cut] if value}
            right = {b for b, value in events[cut:hi] if value}
            assert min(len(left), len(right)) >= radius-radius//2


def test_filtered_trace(trace, address_count):
    memory = [0] * address_count
    events = []
    last = {}
    witnesses = {}
    edges = set()
    for i, (a, kind) in enumerate(trace):
        value = kind-1 if kind else memory[a]
        if not kind and value:
            start = last[a]
            assert events[start] == (a, value)
            competitors = {b for b, carried in events[start+1:] if carried}
            assert a not in competitors
            edges.update((a, b) for b in competitors)
            if a not in witnesses or len(competitors) > witnesses[a][0]:
                witnesses[a] = (len(competitors), start, i)
        last[a] = i
        if kind:
            memory[a] = value
        events.append((a, value))
    degrees = sorted((item[0] for item in witnesses.values()), reverse=True)
    h = sum(d >= rank for rank, d in enumerate(degrees, 1))
    assert len(edges) >= h*h
    check_shared_cut(events, witnesses, h)
    for capacity in range(1, address_count+1):
        cache = {}
        tombstones = {}
        tombstone_errors = set()
        errors = set()
        for (a, kind), (_, value) in zip(trace, events):
            predicted = tombstones.get(a, 0)
            if not kind and predicted != value:
                tombstone_errors.add(a)
            if value:
                tombstones.pop(a, None)
                tombstones[a] = value
                if len(tombstones) > capacity:
                    del tombstones[next(iter(tombstones))]
            elif kind and a in tombstones:
                tombstones[a] = 0
            guess = cache.pop(a, 0)
            if not kind and guess != value:
                errors.add(a)
            if value:
                cache[a] = value
                if len(cache) > capacity:
                    del cache[next(iter(cache))]
        possible = {a for a, (d, _, _) in witnesses.items() if d >= capacity}
        assert errors <= possible and tombstone_errors == possible
        if h < capacity:
            assert len(errors) < capacity
    return h, witnesses


def batch_examples():
    checked = 0
    for h in (4, 8, 12, 16):
        for width in (1, 2, 3, h):
            trace = []
            for start in range(0, h, width):
                batch = range(start, min(h, start+width))
                trace.extend((a, 2) for a in batch)
                trace.extend((a, 2) for a in range(h, 2*h))
                trace.extend((a, 0) for a in batch)
            actual, witnesses = test_filtered_trace(trace, 2*h)
            assert actual == h
            occupancy = [sum(lo < cut <= hi for _, lo, hi in witnesses.values())
                         for cut in range(len(trace)+1)]
            assert max(occupancy) == width
            checked += 1
    return checked


if __name__ == '__main__':
    count = 0
    for alphabet_size, maxlen in ((2, 6), (3, 4)):
        ops = tuple(product(range(alphabet_size), range(3)))
        for length in range(maxlen + 1):
            for raw in product(ops, repeat=length):
                test_trace(raw, alphabet_size)
                test_filtered_trace(raw, alphabet_size)
                count += 1
    for alphabet_size in range(2, 33):
        full_passes(alphabet_size)
    multivalue = 0
    for raw in product(tuple(product(range(2), range(4))), repeat=4):
        test_filtered_trace(raw, 2)
        multivalue += 1
    print(f'{count} read/write histories and 31 complete directed-gap graphs verified.')
    print(f'{count} positive-touch histories, {multivalue} multi-value runs, '
          f'and {batch_examples()} shared-window families verified.')
