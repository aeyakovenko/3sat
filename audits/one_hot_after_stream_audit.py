"""Check exact one-hot probe costs and a degree-four SAT family on actual bytes."""

from collections import Counter, defaultdict
from functools import lru_cache

from one_byte_dense_successor_audit import clause, encode, parse
from selector_parity_cube_audit import Names, physical_template
from switch_index_checksum_audit import check_verdict, cycle_period, streamed


def state_partitions(size):
    """Enumerate all partitions as unordered tuples of disjoint bit masks."""
    if size == 0:
        yield ()
        return
    bit = 1 << (size - 1)
    for parts in state_partitions(size - 1):
        for j, group in enumerate(parts):
            yield parts[:j] + (group | bit,) + parts[j + 1:]
        yield parts + (bit,)


@lru_cache(maxsize=None)
def tree_errors(group, positive, probes):
    """Minimum mistakes for a deterministic membership-probe tree on a known query."""
    best = min(positive.bit_count(), (group ^ positive).bit_count())
    if probes == 0 or best == 0:
        return best
    available = group
    while available:
        slot = available & -available
        available ^= slot
        # A hit identifies one site; the miss branch retains the other sites.
        misses = tree_errors(group ^ slot, positive & ~slot, probes - 1)
        best = min(best, misses)
    return best


def exhaustive_game():
    budgets = games = 0
    for size in range(1, 8):
        # Up to S states allows any partition with at most S nonempty groups.
        best = {}
        for partition in state_partitions(size):
            for probes in range(size // 2 + 1):
                worst = max(
                    sum(tree_errors(group, label & group, probes) for group in partition)
                    for label in range(1 << size)
                )
                key = len(partition), probes
                best[key] = min(best.get(key, size), worst)
                games += 1
        for states in range(1, size + 3):
            zero_error = None
            for probes in range(size // 2 + 1):
                optimal = min(best[s, probes] for s in range(1, min(states, size) + 1))
                excess = max(0, size - states * (2 * probes + 1))
                assert optimal == (excess + 1) // 2
                budgets += 1
                if optimal == 0 and zero_error is None:
                    zero_error = probes
            assert zero_error == ((size + states - 1) // states) // 2
    return games, budgets


def implication_rows(_first, _second, arity):
    assert arity % 2 == 0
    count = arity // 2
    names = Names()
    data = [names.new() for _ in range(count)]
    query = [names.new() for _ in range(count)]
    rows = []
    for x, y in zip(data, query):
        extra = names.new()
        rows.extend(((-x, y, extra), (-x, y, -extra)))
    return rows, data + query


def coordinate(base, selector):
    p, q, a, b = selector
    marker = f'\n{p} {q} {a} 0'.encode()
    assert base.count(marker) == 1 and b == a + 1
    offset = base.index(marker) + len(marker) - 3
    assert base[offset] == ord('2') and str(b).endswith('3')
    return offset


def word_width(bit_length, coefficient):
    # ceil(D log2(n+2)), then round up to a multiple of 16.
    ceiling_log = ((bit_length + 2) ** coefficient - 1).bit_length()
    return 16 * ((ceiling_log + 15) // 16)


def physical_game(size=18):
    fixed, selectors, variables = physical_template([], [], 2*size, h=4,
                                                    semantic_builder=implication_rows)
    base = encode(fixed | {clause(p, q, a) for p, q, a, b in selectors})
    coords = [coordinate(base, row) for row in selectors]
    data, query = coords[:size], coords[size:]
    assert coords == sorted(set(coords))
    bit_length = 8 * len(base)
    for coefficient in (1, 2, 4):
        width = word_width(bit_length, coefficient) // 8
        assert all(x // width < y // width for x, y in zip(coords, coords[1:]))

    def make(index, marked):
        raw = bytearray(base)
        for j in marked:
            raw[query[j]] ^= 1
        if index is not None:
            raw[data[index]] ^= 1
        return bytes(raw)

    # An actual prefix streaming state, computed on the literal file up to
    # (but excluding) the first index-query digit.
    states = [streamed(make(i, set())[:query[0]], 7) for i in range(size)]
    groups = defaultdict(list)
    for i, state in enumerate(states):
        groups[state].append(i)
    state, group = max(groups.items(), key=lambda item: len(item[1]))
    positive = set(group[::2])
    center = make(None, positive)
    target = len(group) // 2
    assert target >= 3

    def trace(raw):
        width = word_width(bit_length, 4) // 8
        def read(site):
            address = data[site] // width
            start = width * address
            reply = int.from_bytes(raw[start:start+width], 'little')
            return address, reply
        k = (state + len(positive)) % len(group)
        first_site = group[k]
        first = read(first_site)
        shift = 8 * (data[first_site] % width)
        changed = (first[1] >> shift) & 1
        next_site = group[(k + 1 + changed) % len(group)]
        second = read(next_site)
        assert first[0] != second[0]
        return first, second

    center_trace = trace(center)
    assert len({trace(make(i, positive))[1][0] for i in group}) == 2
    # Independent prime-power check for every possible radix modulo m <= 8.
    bound = 8
    period = cycle_period(bound, all_bases=True)
    powers = {}
    for site in data:
        exponent = query[0] - site - 1
        assert exponent >= (bound - 1).bit_length()
        signature = tuple(pow(base, exponent, m) for m in range(1, bound+1)
                          for base in range(m))
        key = exponent % period
        assert powers.setdefault(key, signature) == signature
    assert len(powers) < size
    ref_histogram = Counter(make(0, positive))
    unchanged = Counter()
    for i in range(size):
        raw = make(i, positive)
        assert len(raw) == len(base) and Counter(raw) == ref_histogram
        assert [j for j, (a, b) in enumerate(zip(raw, center)) if a != b] == [data[i]]
        assert raw[data[i]] ^ center[data[i]] == 1
        rows = parse(raw)
        degrees = Counter(abs(z) for row in rows for z in row)
        assert encode(rows) == raw and set(degrees) == set(range(1, variables+1))
        assert max(degrees.values()) == 4
        check_verdict(rows, i in positive)
        assert streamed(raw[:query[0]], 7) == states[i]
        if states[i] == state and trace(raw) == center_trace:
            unchanged[i in positive] += 1
    assert min(unchanged[True], unchanged[False]) >= target - len(center_trace)
    print(f'{size} one-hot files, {len(base):,} bytes, {variables:,} variables, '
          f'{len(rows):,} clauses; all parsed verdicts checked')
    print(f'prefix residues mod 7: {sorted((s, len(g)) for s,g in groups.items())}; '
          f'chosen residue {state}, fiber size {len(group)}')
    print(f'two adaptive packed-word reads; identical trace on {unchanged[True]} SAT '
          f'and {unchanged[False]} UNSAT files')


if __name__ == '__main__':
    games, budgets = exhaustive_game()
    print(f'{games:,} partition/probe budgets checked over every query vector; '
          f'{budgets:,} optimal state/probe budgets through D=7')
    physical_game()
