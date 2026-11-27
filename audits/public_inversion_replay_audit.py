"""Finite semantic audit of checked inversion on one proposed native event stream.

The tiny exact index is a reference table. Asymptotic inversion bounds come from
Fiat–Naor. No claim about the reference table's size follows from these tests.
"""

from collections.abc import Callable
from itertools import product
from typing import NamedTuple


class Cpu(NamedTuple):
    pc: int = 0
    index: int = 0
    key: int = 0
    register: int = 1


Store = tuple[int, int] | None
Row = tuple[Cpu, Store, tuple[int, int] | None]
Key = tuple[int, int, int]


def instruction(cpu: Cpu, data: tuple[int, ...], load: Callable[[int], int]) -> Row:
    pc, i, key, reg = cpu
    if pc == 0:
        return Cpu(1, i, data[i] if 0 <= i < len(data) else 0, reg), None, None
    if pc == 1:
        return Cpu(2, i, key, reg), (key, reg), None
    if pc == 2:
        addr = (key ^ reg) & 3
        value = load(addr)
        return Cpu(3, i, key, value), None, (addr, value)
    if pc == 3:
        return Cpu(int(i + 1 == len(data)) * 4, i + 1, key, (reg + key + 1) & 3), None, None
    return cpu, None, None


def actual(data: tuple[int, ...]) -> list[Row]:
    state = Cpu()
    memory: dict[int, int] = {}
    rows: list[Row] = []
    while state.pc != 4:
        row = instruction(state, data, lambda key: memory.get(key, 0))
        state, store, _ = row
        if store is not None:
            key, value = store
            memory[key] = value
        rows.append(row)
    return rows


def dyadics(lo: int, hi: int):
    """Disjoint dyadic cover of [lo, hi), in left-to-right order."""
    while lo < hi:
        size = 1 << ((hi - lo).bit_length() - 1)
        if lo:
            size = min(size, lo & -lo)
        yield lo, size
        lo += size


def store_key(store: Store, t: int, size: int) -> Key:
    # Addresses in this audit are nonnegative, so -1 tags a nonstore.
    return (t // size) * size, size, -1 if store is None else store[0]


def index_rows(stores: list[Store]) -> dict[Key, int]:
    index = {}
    height = (len(stores) - 1).bit_length()
    for t, store in enumerate(stores):
        for level in range(height + 1):
            index[store_key(store, t, 1 << level)] = t
    return index


def checked(stores: list[Store], index: dict[Key, int], key: Key) -> int | None:
    t = index.get(key)
    if t is not None and 0 <= t < len(stores) and store_key(stores[t], t, key[1]) == key:
        return t
    return None


def passes_image_challenges(stores: list[Store], index: dict[Key, int]) -> bool:
    return all(checked(stores, index, key) is not None for key in index_rows(stores))


def previous(stores: list[Store], index: dict[Key, int], addr: int, t: int) -> int | None:
    for lo, size in reversed(tuple(dyadics(0, t))):
        if checked(stores, index, (lo, size, addr)) is None:
            continue
        while size > 1:
            size //= 2
            if checked(stores, index, (lo + size, size, addr)) is not None:
                lo += size
        return lo
    return None


def blocks(data, span, endpoints, read):
    clock = 4 * len(data)
    for lo in range(0, clock, span):
        state = endpoints[lo]
        for t in range(lo, min(lo + span, clock)):
            row = instruction(state, data, lambda addr, time=t: read(time, addr))
            state = row[0]
            yield row


def verify(data, span, endpoints, stores, replies, index):
    clock = 4 * len(data)
    if endpoints[0] != Cpu() or endpoints[clock].pc != 4:
        return False

    def lookup(t, addr):
        p = previous(stores, index, addr, t)
        if p is None:
            return 0
        word = stores[p]
        return 0 if word is None else word[1]

    if replies is None:
        rows = list(blocks(data, span, endpoints, lookup))
    else:
        # On an arbitrary description the entire speculative stream is still
        # deterministic, even before any boundary or memory check has passed.
        rows = list(blocks(data, span, endpoints, lambda t, _: replies[t]))
        stores = [store for _, store, _ in rows]
    if not passes_image_challenges(stores, index):
        return False
    for t, (state, store, load) in enumerate(rows):
        if t + 1 in endpoints and state != endpoints[t + 1]:
            return False
        if store != stores[t] or (load is not None and lookup(t, load[0]) != load[1]):
            return False
    return True


def legal_sources(stores, local_reads, sources):
    """One existential invalidation among all proposed producers rejects a block."""
    for (time, addr, value), source in zip(local_reads, sources, strict=True):
        if source is None:
            if value != 0:
                return False
            first = 0
        else:
            if source >= time or stores[source] != (addr, value):
                return False
            first = source + 1
        if any(stores[t] is not None and stores[t][0] == addr for t in range(first, time)):
            return False
    return True


def test_source_list_checks() -> int:
    from itertools import combinations_with_replacement

    checked_count = 0
    options = [None, (0, 0), (0, 1), (1, 1)]
    for stores in product(options, repeat=3):
        for times in combinations_with_replacement(range(4), 2):
            for keys in product(range(2), repeat=2):
                true = [next((t for t in reversed(range(bound))
                              if stores[t] is not None and stores[t][0] == key), None)
                        for bound, key in zip(times, keys, strict=True)]
                values = [stores[t][1] if t is not None else 0 for t in true]
                for proposals in product((None, 0, 1, 2), repeat=2):
                    local_reads = list(zip(times, keys, values, strict=True))
                    assert legal_sources(stores, local_reads, proposals) == (proposals == tuple(true))
                    checked_count += 1
                for j in (0, 1):
                    altered = values.copy()
                    altered[j] ^= 1
                    assert not legal_sources(stores, list(zip(times, keys, altered, strict=True)), true)
                    checked_count += 1
    return checked_count


def main() -> None:
    runs = accesses = rejected = hidden = 0
    for length in range(1, 5):
        for data in product(range(4), repeat=length):
            rows = actual(data)
            stores = [store for _, store, _ in rows]
            replies = [0 if load is None else load[1] for _, _, load in rows]
            index = index_rows(stores)
            clock = len(rows)
            for addr in range(5):
                direct = None
                for t in range(clock + 1):
                    assert previous(stores, index, addr, t) == direct
                    accesses += 1
                    if t < clock and stores[t] is not None and stores[t][0] == addr:
                        direct = t
            for key in index:
                bad = index.copy()
                bad[key] = clock
                assert not passes_image_challenges(stores, bad)
                hidden += 1
            for span in {1, 3, 5, clock}:
                endpoints = {t: rows[t - 1][0] for t in range(span, clock, span)}
                endpoints.update({0: Cpu(), clock: rows[-1][0]})
                for mode in (None, replies):
                    assert verify(data, span, endpoints, stores, mode, index)
                    for time, state in endpoints.items():
                        changed = dict(endpoints)
                        changed[time] = state._replace(register=state.register ^ 1)
                        assert not verify(data, span, changed, stores, mode, index)
                        rejected += 1
                for t, (_, store, load) in enumerate(rows):
                    if store is not None:
                        altered = stores.copy()
                        altered[t] = (store[0], store[1] ^ 1)
                        assert not verify(data, span, endpoints, altered, None, index_rows(altered))
                        rejected += 1
                    if load is not None:
                        altered = replies.copy()
                        altered[t] ^= 1
                        speculative = list(blocks(data, span, endpoints, lambda i, _, words=altered: words[i]))
                        speculative_index = index_rows([word for _, word, _ in speculative])
                        assert not verify(data, span, endpoints, stores, altered, speculative_index)
                        rejected += 1
            runs += 1
    batch_checks = test_source_list_checks()
    print(f"{runs} computations, {accesses} predecessor comparisons, {hidden} omitted-key"
          f" challenges, {rejected} corrupted field/boundary checks, {batch_checks} "
          "batched-source checks")


if __name__ == "__main__":
    main()
