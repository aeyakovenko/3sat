"""Exhaust fixed block menus and compare local last-writer tests with direct replay."""

from dataclasses import dataclass
from itertools import combinations, product


@dataclass(frozen=True)
class Event:
    op: str
    address: int = 0
    value: int = 0


@dataclass(frozen=True)
class Fault:
    read_time: int
    address: int
    reply: int
    writer_time: int   # -1 denotes the zero-initialized cell
    previous: int

    def fits(self, time, event):
        if time == self.read_time:
            return event == Event("read", self.address, self.reply)
        if time == self.writer_time:
            return event == Event("store", self.address, self.previous)
        if self.writer_time < time < self.read_time:
            return event.op != "store" or event.address != self.address
        return True


def all_faults(length, addresses):
    for t in range(length):
        for address in addresses:
            yield Fault(t, address, 1, -1, 0)
            for s in range(t):
                for v in (0, 1):
                    yield Fault(t, address, 1 - v, s, v)


def replay_faults(blocks):
    latest = {}
    result = set()
    time = 0
    for block in blocks:
        for event in block:
            if event.op == "store":
                latest[event.address] = (time, event.value)
            elif event.op == "read":
                s, v = latest.get(event.address, (-1, 0))
                if event.value != v:
                    result.add(Fault(time, event.address, event.value, s, v))
            time += 1
    return result


def check_families(menus_by_position, block_lengths, addresses):
    faults = tuple(all_faults(sum(block_lengths), addresses))
    # Each local choice must meet *all* timestamp requirements in its block.
    # Distinct blocks may choose their witnesses independently.
    local_masks = []
    offset = 0
    for menus, length in zip(menus_by_position, block_lengths):
        by_menu = {}
        for menu in menus:
            assert all(len(block) == length for block in menu)
            admitted = {
                fault for fault in faults
                if any(all(fault.fits(offset + i, e) for i, e in enumerate(block))
                       for block in menu)
            }
            by_menu[menu] = admitted
        local_masks.append(by_menu)
        offset += length

    chart_count = path_count = empty_count = singleton_count = valid_count = 0
    replay_cache = {}
    for chart in product(*menus_by_position):
        chart_count += 1
        weak_paths = set(product(*chart))
        path_count += len(weak_paths)
        nonempty = all(chart)
        singleton = nonempty and all(len(set(menu)) == 1 for menu in chart)
        assert bool(weak_paths) == nonempty
        assert (len(weak_paths) == 1) == singleton
        local_faults = set(faults)
        for menu, admitted in zip(chart, local_masks):
            local_faults &= admitted[menu]
        actual_faults = set()
        for path in weak_paths:
            if path not in replay_cache:
                replay_cache[path] = replay_faults(path)
            actual_faults.update(replay_cache[path])
        assert local_faults == actual_faults
        empty_count += not nonempty
        singleton_count += singleton
        valid_count += nonempty and not actual_faults
    return chart_count, path_count, empty_count, singleton_count, valid_count


def main():
    quiet = Event("quiet")
    w0, w1 = (Event("store", 0, v) for v in (0, 1))
    r0, r1 = (Event("read", 0, v) for v in (0, 1))
    other = Event("store", 1, 1)
    alphabet = tuple((e,) for e in (quiet, w0, w1, r0, r1))
    menus = tuple(menu for size in (0, 1, 2) for menu in combinations(alphabet, size))
    regular = check_families([menus] * 3, [1] * 3, [0])
    # The middle block can correlate two choices. The repeated alternative
    # represents two different witnesses projecting to the same visible trace.
    middle = ((), ((w0, r0), (w1, r1)), ((w1, other), (quiet, w0)),
              ((r1, quiet), (r1, quiet)), ((quiet, other),), ((r0, w1),))
    mixed = check_families([menus, middle, menus], [1, 2, 1], [0, 1])
    assert not replay_faults(((w0,), (w1,), (r1,)))
    assert replay_faults(((w1,), (other,), (r0,))) == {Fault(2, 0, 0, 0, 1)}
    assert all(not replay_faults((block,)) for block in ((w0, r0), (w1, r1)))
    print("charts, projected paths, empty, singleton, nonempty all-valid")
    print("single-slot menus:", regular)
    print("mixed two-address menus:", mixed)


if __name__ == "__main__":
    main()
