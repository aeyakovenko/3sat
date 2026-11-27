"""Finite audit of per-address write-patch, read-source, and unlisted scratch."""

from collections import Counter, defaultdict
from itertools import product


def simulate_interval(instructions, incoming):
    """Only the first read before a local write needs an incoming word."""
    needed, writes, observations = {}, {}, []

    def load(a):
        if a in writes:
            return writes[a]
        if a not in needed:
            needed[a] = incoming(a)
        return needed[a]

    for op, a, v in instructions:
        if op == "w":
            writes[a] = v
        elif op == "r":
            observations.append(load(a))
        elif op == "indirect":
            observations.append(load(a + load(v)))
        else:
            raise ValueError(op)
    return needed, writes, tuple(observations)


def trace(intervals):
    """Construct honest records independently by chronological execution."""
    memory, last_writer = {}, {}
    deltas, reads, observations = {}, {}, []
    for i, instructions in enumerate(intervals):
        start, written = memory.copy(), set()

        def load(a):
            if a not in written:
                reads[i, a] = (last_writer.get(a, -1), start.get(a, 0))
            return memory.get(a, 0)

        local = []
        for op, a, v in instructions:
            if op == "w":
                written.add(a)
                memory[a] = v
            elif op == "r":
                local.append(load(a))
            elif op == "indirect":
                local.append(load(a + load(v)))
            else:
                raise ValueError(op)
        for a in written:
            if i + 1 < len(intervals) and memory[a] != start.get(a, 0):
                deltas[i, a] = memory[a]
            last_writer[a] = i
        observations.append(tuple(local))
    return deltas, reads, tuple(observations)


def minimum_chart(deltas, reads):
    write_counts = Counter(a for i, a in deltas)
    read_counts = Counter(a for i, a in reads)
    modes = {a: ("write" if write_counts[a] <= read_counts[a] else "read")
             for a in write_counts.keys() & read_counts.keys()}
    patches = {key: v for key, v in deltas.items() if modes.get(key[1]) == "write"}
    records = {key: v for key, v in reads.items() if modes.get(key[1]) == "read"}
    assert len(patches) + len(records) == sum(
        min(write_counts[a], read_counts[a]) for a in write_counts.keys() | read_counts.keys())
    return modes, patches, records


def verify(intervals, modes, patches, records):
    """Enumerate all local and pair challenges, without a global scratch simulation."""
    size = len(intervals)
    if any(mode not in ("write", "read") for mode in modes.values()):
        return None
    if any(not 0 <= i < size - 1 or modes.get(a) != "write" for i, a in patches):
        return None
    if any(not 0 <= i < size or modes.get(a) != "read" for i, a in records):
        return None
    patch_history = defaultdict(list)
    for (i, a), v in sorted(patches.items()):
        patch_history[a].append((i, v))

    def predecessor(i, a):
        return next((v for j, v in reversed(patch_history[a]) if j < i), 0)

    needed, writes, observations = {}, {}, {}
    try:
        for i in reversed(range(size)):
            def incoming(a):
                if modes.get(a) == "write":
                    return predecessor(i, a)
                if modes.get(a) == "read":
                    return records[i, a][1]
                return 0

            needed[i], writes[i], observations[i] = simulate_interval(intervals[i], incoming)
            if i + 1 < size:
                declared = {a: v for (j, a), v in patches.items() if j == i}
                for a in writes[i].keys() | declared.keys():
                    if modes.get(a) != "write":
                        continue
                    old = predecessor(i, a)
                    actual = writes[i].get(a, old)
                    if (a in declared) != (old != actual) or declared.get(a, old) != actual:
                        return None
    except KeyError:
        return None  # A read-mode interval used an incoming word without a record.

    for (i, a), (source, value) in records.items():
        if a not in needed[i] or not -1 <= source < i:
            return None
        if source == -1:
            if value != 0:
                return None
        elif writes[source].get(a) != value:
            return None
        if any(a in writes[j] for j in range(source + 1, i)):
            return None  # Intervening writes also count if they wrote the same value.
    for i in range(size):
        for a in needed[i]:
            if a not in modes and any(writes[j].get(a, 0) != 0 for j in range(i)):
                return None
    return tuple(observations[i] for i in range(size))


def main():
    a, b = 2**39, 2**47
    write_a, erase_a, read_a = ("w", a, 1), ("w", a, 0), ("r", a, 0)
    write_b, read_b = ("w", b, 2), ("r", b, 0)
    indirect = ("indirect", a, b)
    counts = Counter()

    def audit(intervals):
        deltas, reads, observations = trace(intervals)
        modes, patches, records = minimum_chart(deltas, reads)
        assert verify(intervals, modes, patches, records) == observations
        counts["honest"] += 1
        if set(modes.values()) == {"write", "read"}:
            counts["mixed"] += 1

        def reject(category, proposed_modes, proposed_patches, proposed_records):
            assert verify(intervals, proposed_modes, proposed_patches, proposed_records) is None
            counts[category] += 1

        for key, (source, value) in records.items():
            i, _ = key
            reject("missing read", modes, patches, {k: v for k, v in records.items() if k != key})
            reject("wrong source", modes, patches, {**records, key: (i, value)})
            reject("wrong read value", modes, patches, {**records, key: (source, value + 1)})
            if source >= 0:
                reject("fake initial zero", modes, patches, {**records, key: (-1, 0)})
            if source >= 1:
                reject("stale source", modes, patches, {**records, key: (source - 1, value)})
        for key, value in patches.items():
            reject("omitted delta", modes, {k: v for k, v in patches.items() if k != key}, records)
            reject("wrong delta", modes, {**patches, key: value + 1}, records)
        return modes, patches, records

    choices = [(write_a,), (erase_a,), (read_a,), (write_b,), (read_b,),
               (write_a, erase_a, read_a), (read_a, read_a), (indirect,)]
    for intervals in product(choices, repeat=3):
        audit(intervals)

    # In address a's read mode the last writer is required even across a
    # same-value write. At b one erasure or value change can feed many reads.
    intervals = [(write_a, write_b), (erase_a,), (write_a,), (write_a,),
                 (read_a, read_b, read_b), (read_b,), (read_b,)]
    modes, patches, records = audit(intervals)
    assert modes == {a: "read", b: "write"} and records[4, a] == (3, 1)
    assert verify(intervals, modes, patches, {**records, (4, a): (2, 1)}) is None
    counts["stale same-value source"] += 1
    assert verify(intervals, modes, patches, {**records, (3, a): (2, 1)}) is None
    counts["unused read claim"] += 1
    assert verify(intervals, {b: "write"}, patches, {}) is None
    counts["unlisted conflict"] += 1

    intervals = [(write_a,), (erase_a,), (write_a,), (erase_a,), (read_a, indirect)]
    modes, patches, records = audit(intervals)
    assert records[4, a] == (3, 0)
    assert verify(intervals, modes, patches, {(4, a): (-1, 0)}) is None
    counts["erasure source"] += 1

    intervals = [(read_a,), (write_a,), (erase_a,), (write_a,), (read_b,)]
    modes, patches, records = audit(intervals)
    assert records[0, a] == (-1, 0)
    counts["honest initial zero"] += 1

    intervals = [[("w", a + 2, 17), write_b], [indirect], [read_b]]
    modes, patches, records = audit(intervals)
    assert verify(intervals, modes, patches, records)[1] == (17,)
    counts["nonzero indirect read"] += 1
    print(", ".join(f"{n} {label}" for label, n in counts.items()))


if __name__ == "__main__":
    main()
