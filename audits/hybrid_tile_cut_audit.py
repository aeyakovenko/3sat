"""Compare native hybrid execution with independent tile-group replay on exact checkpoints."""

from collections import defaultdict
from copy import deepcopy
from dataclasses import dataclass
from itertools import product
from random import Random


def tile_key(position, width, shift):
    return tuple((x - shift) // width for x in position)


def step(time, position, register, tape, auxiliary, public):
    """Two sparse words per five steps, with fresh addresses in subsequent rounds."""
    dimension = len(position)
    round_index, phase = divmod(time, 5)
    first = 70001 * round_index + 1009
    second = first + 51117
    old = tape.get(position, 0)
    datum = public[(register + old + time) % len(public)]
    incoming = auxiliary.get(first if phase % 2 == 0 else second, 0)
    if phase == 0:
        auxiliary[first] = 1 + (datum ^ old)
    elif phase == 1:
        auxiliary[second] = 1 + (register ^ datum)
    elif phase == 3:
        auxiliary.pop(first, None)
    elif phase == 4:
        auxiliary.pop(second, None)
    register = (register * 5 + incoming + old + datum + time) % 251
    value = (register ^ datum) % 5
    if value:
        tape[position] = value
    else:
        tape.pop(position, None)
    axis = (time // 14) % dimension
    delta = 1 if time % 14 < 7 else -1
    if (datum + register) % 11 == 0:
        delta = 0
    target = list(position)
    target[axis] += delta
    return tuple(target), register


@dataclass
class Chart:
    times: list
    keys: list
    cpu: list
    ram: list
    photos: dict


def groups(times, keys, budget):
    by_key = defaultdict(list)
    for index, key in enumerate(keys):
        by_key[key].append(index)
    for key, visits in by_key.items():
        blocks = []
        current, duration = [], 0
        for index in visits:
            current.append(index)
            duration += times[index + 1] - times[index]
            if duration >= budget:
                blocks.append(current)
                current, duration = [], 0
        if current:
            blocks.append(current)
        yield key, blocks


def make_chart(clock, dimension, width, budget, public):
    position, register = (0,) * dimension, 0
    tape, auxiliary, history = {}, {}, []
    for time in range(clock + 1):
        assert 0 <= len(auxiliary) <= 2
        history.append((position, register, tuple(sorted(auxiliary.items())), dict(tape)))
        if time < clock:
            position, register = step(time, position, register, tape, auxiliary, public)
    assert len({a for _, _, sparse, _ in history for a, _ in sparse}) > 10
    candidates = []
    for shift in range(width):
        keys = [tile_key(pos, width, shift) for pos, _, _, _ in history]
        crossings = [t for t in range(1, clock + 1) if keys[t] != keys[t - 1]]
        candidates.append((len(crossings), shift, crossings, keys))
    count, shift, crossings, all_keys = min(candidates)
    assert count <= clock // width
    times = sorted({0, clock, *crossings, *range(budget, clock, budget)})
    keys = [all_keys[t] for t in times[:-1]]
    photos = {}
    for key, blocks in groups(times, keys, budget):
        for block in blocks[1:]:
            first = block[0]
            photos[first] = {addr: value for addr, value in history[times[first]][3].items()
                             if tile_key(addr, width, shift) == key}
    assert len(photos) <= clock // budget
    return shift, Chart(times, keys, [(history[t][0], history[t][1]) for t in times],
                        [history[t][2] for t in times], photos)


def validates(chart, clock, dimension, width, shift, budget, public):
    times, keys, cpu, ram = chart.times, chart.keys, chart.cpu, chart.ram
    if not (times[0] == 0 and times[-1] == clock and
            len(keys) + 1 == len(cpu) == len(ram) == len(times)):
        return False
    if any(not 0 < b - a <= budget for a, b in zip(times, times[1:])):
        return False
    if cpu[0] != ((0,) * dimension, 0) or ram[0]:
        return False
    for listing in ram:
        addresses = [address for address, value in listing]
        if (len(listing) > 2 or addresses != sorted(set(addresses)) or
                any(value == 0 for _, value in listing)):
            return False
    consumed = set()
    for key, blocks in groups(times, keys, budget):
        for j, block in enumerate(blocks):
            start = block[0]
            if j == 0:
                tape = {}
            else:
                if start not in chart.photos:
                    return False
                consumed.add(start)
                tape = dict(chart.photos[start])
            duration = 0
            for i in block:
                pos, reg = cpu[i]
                auxiliary = dict(ram[i])
                for t in range(times[i], times[i + 1]):
                    if tile_key(pos, width, shift) != key:
                        return False
                    pos, reg = step(t, pos, reg, tape, auxiliary, public)
                    duration += 1
                if cpu[i + 1] != (pos, reg):
                    return False
                # Comparing only listed values fails on hidden nonzero entries.
                if len(auxiliary) != len(ram[i + 1]) or any(
                        auxiliary.get(a) != v for a, v in ram[i + 1]):
                    return False
            assert duration <= 2 * budget
            if j + 1 < len(blocks) and chart.photos.get(blocks[j + 1][0]) != tape:
                return False
    return consumed == set(chart.photos)


def main():
    truthful, rejected, images = 0, 0, 0
    for seed, dimension, width, budget in product(range(6), (1, 2, 3), (2, 3, 4), (5, 11)):
        public = list(range(29))
        Random(seed).shuffle(public)
        clock = 83
        shift, chart = make_chart(clock, dimension, width, budget, public)
        def passes(candidate):
            return validates(candidate, clock, dimension, width, shift, budget, public)
        assert passes(chart)
        truthful += 1
        for i in range(1, len(chart.times)):
            bad = deepcopy(chart)
            pos, reg = bad.cpu[i]
            bad.cpu[i] = (pos, reg ^ 1)
            assert not passes(bad)
            rejected += 1
            if chart.ram[i]:
                for mutation in ("remove", "address", "value"):
                    bad = deepcopy(chart)
                    original = bad.ram[i]
                    a, v = original[-1]
                    replacement = {"remove": (), "address": ((99999999, v),),
                                   "value": ((a, v + 1),)}[mutation]
                    bad.ram[i] = original[:-1] + replacement
                    assert not passes(bad)
                    rejected += 1
        for start in chart.photos:
            bad = deepcopy(chart)
            pos = bad.cpu[start][0]
            old = bad.photos[start].get(pos, 0)
            bad.photos[start][pos] = 1 if old != 1 else 2
            assert not passes(bad)
            images += 1
        bad = deepcopy(chart)
        bad.keys[0] = tuple(k + 1 for k in bad.keys[0])
        assert not passes(bad)
        rejected += 1
    assert images > 0
    print(f"{truthful} hybrid traces accepted; {rejected} CPU, sparse-array, or tile-label "
          f"corruptions and {images} incorrect tile snapshots rejected.")


if __name__ == "__main__":
    main()
