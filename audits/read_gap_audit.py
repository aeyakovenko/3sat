"""Exhaust written/virgin read charts for fixed event schedules on two work cells."""

from itertools import product

IDLE = ("idle", 0, 0)
EVENTS = [IDLE, ("read", 0, 0), ("read", 1, 0)] + [
    ("store", a, v) for a in range(2) for v in range(2)
]


def genuine(events):
    memory = [0, 0]
    previous = [0, 0]
    written = [False, False]
    reads = {}
    for t, (kind, a, v) in enumerate(events, 1):
        if kind == "idle":
            continue
        if kind == "read":
            reads[t] = (previous[a], memory[a], written[a])
        else:
            memory[a], written[a] = v, True
        previous[a] = t
    return reads


def live_area(events):
    area = 0
    for cut in range(len(events)):
        for address in range(2):
            stored = any(k == "store" and a == address for k, a, _ in events[:cut])
            following = next((k for k, a, _ in events[cut:] if k != "idle" and a == address), None)
            area += stored and following == "read"
    return area


def blocks(length, width, phase):
    current = 0
    result = [0]  # Index zero is the sentinel, never a real predecessor in a written read.
    for t in range(1, length + 1):
        if t > 1 and (t - 1) % width == phase:
            current += 1
        result.append(current)
    return result


def check_chart(events, layout, directory):
    local = {}
    trace = {}
    for t, (kind, a, v) in enumerate(events, 1):
        if layout[t] != layout[t - 1]:
            local = {}
        if kind == "idle":
            continue
        if kind == "store":
            value, flag = v, True
        elif a in local:
            _, value, flag = local[a]
        elif t in directory:
            _, value = directory[t]
            flag = True
        else:
            value, flag = 0, False
        local[a] = (t, value, flag)
        trace[t] = (a, value, flag)

    for t, (pred, value) in directory.items():
        kind, a, _ = events[t - 1]
        if kind != "read" or not 0 < pred < t or trace.get(pred) != (a, value, True):
            return False
        if layout[t] == layout[pred]:
            return False
        if any(k != "idle" and addr == a for k, addr, _ in events[pred:t - 1]):
            return False
    for t, (a, _, flag) in trace.items():
        if not flag and any(k == "store" and addr == a for k, addr, _ in events[:t - 1]):
            return False
    return True


def run(length=4):
    count = phases = lost = bad_stamp = 0
    for events in product(EVENTS, repeat=length):
        count += 1
        reads = genuine(events)
        written = {t: (p, v) for t, (p, v, flag) in reads.items() if flag}
        gaps = [t - p for t, (p, _) in written.items()]
        assert live_area(events) == sum(gaps)
        current = 0
        for r in range(1, length + 1):
            before = current
            current += 1 + (r - written[r][0] if r in written else 0)
            assert current <= 2 * before + 2
            assert current == r + live_area(events[:r])
        for width in range(1, length + 2):
            crossings = 0
            for phase in range(width):
                layout = blocks(length, width, phase)
                directory = {t: (p, v) for t, (p, v) in written.items() if layout[p] != layout[t]}
                crossings += len(directory)
                assert check_chart(events, layout, directory)
                phases += 1
                for t, (p, v) in directory.items():
                    missing = directory.copy()
                    del missing[t]
                    assert not check_chart(events, layout, missing)
                    lost += 1
                    for wrong_p in range(t):
                        if wrong_p != p:
                            assert not check_chart(events, layout, directory | {t: (wrong_p, v)})
                            bad_stamp += 1
            assert crossings == sum(min(width, g) for g in gaps)
    print(f"{count} traces, {phases} authentic phase charts, {lost} missing records, "
          f"{bad_stamp} wrong timestamps checked")


if __name__ == "__main__":
    run()
