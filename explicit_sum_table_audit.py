"""Exhaustive posterior fibers, native record alignment and statistical covering."""

from collections import Counter, defaultdict
from dataclasses import dataclass
from itertools import combinations, product
from random import Random

PARENTS = ((), (), (), (0, 1), (1, 2), (0, 2), (3, 4))


def partition(worlds, selected):
    parts = defaultdict(list)
    for world in worlds:
        parts[tuple(world[p] for p in selected)].append(world)
    return parts.values()


@dataclass
class Posterior:
    worlds: list
    known: frozenset
    failures: tuple
    hits: frozenset
    marks: frozenset
    hit_rounds: tuple


def test_query(state, v, subscript, alphabet, round_id, stats):
    parents = PARENTS[v]
    heavy = tuple(
        p for p in parents if p not in state.known and 2 * state.failures[p] >= alphabet
    )
    known = state.known | frozenset(heavy)
    marked = state.marks | frozenset(heavy)
    fresh = tuple(p for p in parents if p not in known)
    stats["heavy_releases"] += len(heavy)
    for worlds in partition(state.worlds, heavy):
        yes, no = [], []
        fibers = defaultdict(list)
        for world in worlds:
            agrees = sum(world[p] for p in parents) % alphabet == subscript
            (yes if agrees else no).append(world)
            if fresh:
                p = fresh[0]
                fibers[world[:p] + world[p + 1 :]].append(agrees)
        for answers in fibers.values():
            assert 2 * len(answers) > alphabet
            assert sum(answers) <= 1
            assert alphabet * sum(answers) <= 2 * len(answers)
            stats["posterior_fibers"] += 1
            stats["two_unknown_fibers"] += len(fresh) == 2
            stats["previous_failed_fibers"] += state.failures[fresh[0]] > 0
        if no:
            fails = list(state.failures)
            for p in parents:
                fails[p] += 1
            yield Posterior(
                no, known, tuple(fails), state.hits, marked, state.hit_rounds
            )
        for hit_worlds in partition(yes, fresh):
            first = list(state.hit_rounds)
            first[v] = min(round_id, first[v])
            yield Posterior(
                hit_worlds,
                known | frozenset(fresh),
                state.failures,
                state.hits | {v},
                marked | frozenset(fresh),
                tuple(first),
            )


def check_posterior():
    stats = Counter()
    vertices, alphabet = len(PARENTS), 4
    missing = 100
    start = Posterior(
        list(product(range(alphabet), repeat=vertices)),
        frozenset(),
        (0,) * vertices,
        frozenset(),
        frozenset(),
        (missing,) * vertices,
    )
    states = [start]
    batches = (
        ((3, 0), (4, 0), (5, 1)),
        ((5, 2), (3, 3), (6, 0)),
        ((0, 0), (4, 3), (6, 2)),
    )
    for round_id, batch in enumerate(batches):
        next_states = []
        for state in states:
            # This tape's queries depend only on earlier augmented replies.
            witness = state.worlds[0]
            offset = sum(witness[p] for p in state.known) % alphabet
            active = [state]
            for v, bias in batch:
                following = []
                for partial in active:
                    following.extend(
                        test_query(
                            partial,
                            v,
                            (bias + offset) % alphabet,
                            alphabet,
                            round_id,
                            stats,
                        )
                    )
                active = following
            for partial in active:
                released = partial.hits - partial.known
                for worlds in partition(partial.worlds, sorted(released)):
                    next_states.append(
                        Posterior(
                            worlds,
                            partial.known | released,
                            partial.failures,
                            frozenset(),
                            partial.marks,
                            partial.hit_rounds,
                        )
                    )
        states = next_states
        assert sum(len(state.worlds) for state in states) == alphabet**vertices
    for state in states:
        for v, parents in enumerate(PARENTS):
            if state.hit_rounds[v] < missing:
                for p in parents:
                    if p not in state.marks:
                        assert state.hit_rounds[p] < state.hit_rounds[v]
                    stats["edge_checks"] += 1
    assert all(
        stats[k]
        for k in ("heavy_releases", "two_unknown_fibers", "previous_failed_fibers")
    )
    return stats


def selected_records(labels, alphabet):
    return [sum(labels[p] for p in parents) % alphabet for parents in PARENTS]


def evaluate_packed(file, alphabet, table_start, record_bits):
    computed, flags = [], 0
    for v, parents in enumerate(PARENTS):
        key = sum(computed[p] for p in parents) % alphabet
        cell = table_start + v * alphabet + key
        rec = file >> (cell * record_bits) & ((1 << record_bits) - 1)
        computed.append(rec % alphabet)
        flags += (rec // alphabet) & 1
    return computed, flags


def packed_reads(rng):
    stats = Counter()
    for alphabet in (2, 4, 8):
        for _ in range(25):
            labels = [rng.randrange(alphabet) for _ in PARENTS]
            active = selected_records(labels, alphabet)
            flat = [rng.randrange(2 * alphabet) for _ in range(len(PARENTS) * alphabet)]
            for v, key in enumerate(active):
                flat[v * alphabet + key] = labels[v]
            native_bits, record_bits = 17, 23
            header = [len(PARENTS), alphabet]
            topology = [
                sum((p + 1) << (4 * j) for j, p in enumerate(ps)) for ps in PARENTS
            ]
            records = header + topology + flat
            table_start = len(header) + len(topology)
            packed = sum(value << (record_bits * i) for i, value in enumerate(records))
            word_mask = (1 << native_bits) - 1
            for base in range(0, record_bits * len(records), native_bits):
                first, last = (
                    base // record_bits,
                    (base + native_bits - 1) // record_bits,
                )
                reply = records[first]
                if last != first and last < len(records):
                    reply += records[last] << record_bits
                assert (packed >> base & word_mask) == (
                    reply >> (base % record_bits) & word_mask
                )
                stats["unaligned_words"] += 1
            assert evaluate_packed(packed, alphabet, table_start, record_bits) == (
                labels,
                0,
            )
            for count in range(len(PARENTS) + 1):
                for edited in combinations(range(len(PARENTS)), count):
                    other = packed
                    for v in edited:
                        cell = table_start + v * alphabet + active[v]
                        other ^= alphabet << (cell * record_bits)
                    assert evaluate_packed(
                        other, alphabet, table_start, record_bits
                    ) == (labels, count)
                    stats["edited_runs"] += 1
    return stats


def sample_moments(rng):
    checked = 0
    for _ in range(100):
        size = rng.randrange(4, 12)
        tapes = [{v for v in range(size) if rng.randrange(3) == 0} for _ in range(4)]
        for j in (1, 2, 3):
            misses = sum(
                size - len(set().union(*(tapes[i] for i in sample)))
                for sample in product(range(len(tapes)), repeat=j)
            )
            by_vertex = sum(
                sum(v not in tape for tape in tapes) ** j for v in range(size)
            )
            assert misses == by_vertex
            checked += 1
    return checked


def binary_fan_in(dag):
    binary, owners, outputs = [], [], []
    for v, parents in enumerate(dag):
        roots = [outputs[p] for p in parents]
        while len(roots) > 2:
            binary.append(tuple(roots[:2]))
            owners.append(v)
            roots = [len(binary) - 1, *roots[2:]]
        binary.append(tuple(roots))
        owners.append(v)
        outputs.append(len(binary) - 1)
    return binary, owners


def longest_path(dag, deleted):
    paths = []
    for v, parents in enumerate(dag):
        pred = max((paths[p] for p in parents), key=len, default=[])
        paths.append([] if v in deleted else [*pred, v])
    return max(paths, key=len, default=[])


def binary_path_checks(rng):
    counts = Counter()
    for _ in range(36):
        dag = [
            tuple(i for i in range(v) if rng.randrange(4) != 0)[:4] for v in range(8)
        ]
        binary, owners = binary_fan_in(dag)
        assert all(len(parents) <= 2 for parents in binary)
        for quota in range(5):
            minimum = len(binary)
            for removed in combinations(range(len(binary)), quota):
                projected = {owners[v] for v in removed}
                minimum_original = len(longest_path(dag, projected))
                remaining = len(longest_path(binary, set(removed)))
                assert remaining >= minimum_original
                counts["binary_deletion_tests"] += 1
                minimum = min(remaining, minimum)
            assert minimum > 0
            marks = set(range(quota // 4))
            newly_used = set()
            while len(marks | newly_used) <= quota:
                path = longest_path(binary, marks | newly_used)[:minimum]
                assert len(path) == minimum
                assert not (set(path) & (marks | newly_used))
                newly_used.update(path)
            assert 2 * len(newly_used) >= quota
            counts["disjoint_path_packings"] += 1
    return counts


if __name__ == "__main__":
    rng = Random(27271)
    counts = check_posterior() + packed_reads(rng) + binary_path_checks(rng)
    counts["private_tape_moments"] = sample_moments(rng)
    print(", ".join(f"{n} {key}" for key, n in sorted(counts.items())))
