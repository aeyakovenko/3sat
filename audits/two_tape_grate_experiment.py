"""Check native path lifting under deleted visits on small two-plane schedules."""

from dataclasses import dataclass, field
from itertools import combinations
from random import Random


def snake(side):
    for y in range(side):
        columns = range(side) if y % 2 == 0 else reversed(range(side))
        for x in columns:
            yield x, y


@dataclass
class Trace:
    visits: list = field(default_factory=lambda: [((0, 0), (0, 0))])
    hubs: dict = field(default_factory=dict)
    ideal_edges: set = field(default_factory=set)

    def go(self, target_a, target_b):
        a, b = self.visits[-1]
        for head, target in enumerate((target_a, target_b)):
            cur = list((a, b)[head])
            for axis in (0, 1):
                while cur[axis] != target[axis]:
                    cur[axis] += 1 if target[axis] > cur[axis] else -1
                    if head == 0:
                        a = tuple(cur)
                    else:
                        b = tuple(cur)
                    self.visits.append((a, b))
        # Give the designated event its own timestamp even after a stay.
        self.visits.append((a, b))
        return len(self.visits) - 1


def make_trace(side, successors):
    order = list(snake(side))
    trace = Trace()

    def tile(v, lane):
        return (v % 2 * side + lane[0], v // 2 * side + lane[1])

    for v, targets in enumerate(successors):
        for lane in order:
            pos = tile(v, lane)
            trace.hubs[v, lane] = trace.go(pos, pos)
        for w in targets:
            for mode in ('identity', 'horizontal', 'vertical'):
                for i, j in order:
                    if mode == 'horizontal':
                        dest = (i + 2 * j + 1) % side, j
                    elif mode == 'vertical':
                        dest = i, (j + 2 * i) % side
                    else:
                        dest = i, j
                    trace.go(tile(v, (i, j)), tile(w, dest))
                    trace.ideal_edges.add(((v, (i, j)), (w, dest)))
    return trace


def check_deletions(trace, removed):
    """Use only consecutive same-cell edges. Time-successor edges are unnecessary."""
    labels = {hub: i for i, hub in enumerate(trace.hubs.values())}
    reached = []
    previous = [{}, {}]
    poisoned = [set(), set()]
    for t, cells in enumerate(trace.visits):
        mask = 0
        for plane, cell in enumerate(cells):
            prior = previous[plane].get(cell)
            if prior is not None:
                mask |= reached[prior]
            previous[plane][cell] = t
            if t in removed:
                poisoned[plane].add(cell)
        if t in labels:
            mask |= 1 << labels[t]
        reached.append(0 if t in removed else mask)

    def clean(hub):
        a, b = trace.visits[hub]
        return a not in poisoned[0] and b not in poisoned[1]

    for src, dst in trace.ideal_edges:
        h, k = trace.hubs[src], trace.hubs[dst]
        if clean(h) and clean(k):
            assert h < k and reached[k] & (1 << labels[h]), (h, k, removed)
    lost = sum(not clean(hub) for hub in trace.hubs.values())
    assert lost <= 2 * len(removed)


def check_timers(n):
    """Check the start-up and subsequent boundary signals against absolute time."""
    s = n + 1
    period = 2 * s
    fast = slow = 0
    fast_dir = slow_dir = 1
    for t in range(period ** 3):
        if fast == 0:
            fast_dir = 1
        elif fast == s:
            fast_dir = -1
        end_cycle = fast == 1 and fast_dir == -1
        if t < period:
            end_epoch = False
            if t == period - 1:
                slow_dir = 1
            else:
                slow += fast_dir
        else:
            if slow == 0:
                slow_dir = 1
            elif slow == s:
                slow_dir = -1
            end_epoch = end_cycle and slow == 1 and slow_dir == -1
            if end_cycle:
                slow += slow_dir
        fast += fast_dir
        assert end_epoch == ((t + 1) % (period * period) == 0)
        assert 0 <= fast <= s and 0 <= slow <= s


def main():
    rng = Random(31)
    count = 0
    for n in range(2, 18):
        check_timers(n)
    print('All epoch-boundary signals checked for command lengths 2 through 17')
    for side, successors in [(2, ((1,), ())), (3, ((1, 2), (2, 3), (3,), ())),
                             (4, ((1, 3), (2,), (3,), ()))]:
        trace = make_trace(side, successors)
        times = range(len(trace.visits))
        for t in times:
            check_deletions(trace, {t})
            count += 1
        if side == 2:
            for pair in combinations(times, 2):
                check_deletions(trace, set(pair))
                count += 1
        for _ in range(80):
            check_deletions(trace, set(rng.sample(times, rng.randrange(len(times)//20 + 2))))
            count += 1
        print(f'side {side}: {len(times)} visits, {len(trace.ideal_edges)} ideal edges')
    print(f'{count} deletion tests passed')


if __name__ == '__main__':
    main()
