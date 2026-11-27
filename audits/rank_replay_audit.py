"""Finite checks of reset-history lookup and physically or semantically deferred inputs."""

from bisect import bisect_right
from itertools import combinations, product
from random import Random


class PrefixPredecessor:
    """Precompute direct results at missing radix children, then search digit depth."""

    def __init__(self, ordered_keys, bits, digit_bits):
        self.keys = sorted(ordered_keys)
        self.digit_bits = digit_bits
        self.radix = 1 << digit_bits
        self.depth = (bits + digit_bits - 1) // digit_bits
        self.width = self.depth * digit_bits
        self.nodes = {}
        if not self.keys:
            return
        for key in self.keys:
            for depth in range(self.depth + 1):
                prefix = key >> (self.width - depth * digit_bits)
                self.nodes[depth, prefix] = None
        for depth, prefix in tuple(self.nodes):
            if depth == self.depth:
                continue
            child_width = self.width - (depth + 1) * digit_bits
            table = []
            for digit in range(self.radix):
                ceiling = (((prefix * self.radix + digit) + 1) << child_width) - 1
                before = bisect_right(self.keys, ceiling)
                table.append(self.keys[before - 1] if before else None)
            self.nodes[depth, prefix] = table

    def predecessor(self, key):
        if not self.nodes:
            return None
        lo, hi = 0, self.depth + 1
        while hi - lo > 1:
            mid = (hi + lo) // 2
            prefix = key >> (self.width - mid * self.digit_bits)
            if (mid, prefix) in self.nodes:
                lo = mid
            else:
                hi = mid
        if lo == self.depth:
            return key
        prefix = key >> (self.width - lo * self.digit_bits)
        digit = (key >> (self.width - (lo + 1) * self.digit_bits)) % self.radix
        return self.nodes[lo, prefix][digit]


def check_persistence():
    rng = Random(41143)
    queries = 0
    for _ in range(36):
        width, horizon, addresses = 3, 48, 5
        memory = [0] * addresses
        states = [tuple(memory)]
        changes = [[] for _ in memory]
        resets = [0] * addresses
        for t in range(1, horizon + 1):
            a = rng.choice((0, 0, 0, 1, 2, 3, 4))
            new = rng.randrange(1 << width)
            old = memory[a]
            if new != old:
                resets[a] += (old & ~new).bit_count()
                changes[a].append((t, new))
                memory[a] = new
            states.append(tuple(memory))
        time_bits = horizon.bit_length()
        heavy = {a for a in range(addresses) if len(changes[a]) > 2 * width}
        assert all(len(h) <= width + 2 * d for h, d in zip(changes, resets))
        assert sum(len(changes[a]) for a in heavy) <= 4 * sum(resets)
        values = {(a << time_bits) + t: v for a in heavy for t, v in changes[a]}
        for digit_bits in (1, 2, 3, 4):
            index = PrefixPredecessor(values, addresses.bit_length() + time_bits, digit_bits)
            for t, state in enumerate(states):
                for a, expected in enumerate(state):
                    if a in heavy:
                        found = index.predecessor((a << time_bits) + t)
                        answer = values[found] if found is not None and found >> time_bits == a else 0
                    else:
                        answer = next((v for date, v in reversed(changes[a]) if date <= t), 0)
                    assert answer == expected
                    queries += 1
    return queries


def panel_step(colors, i, controller, memory, clock, probe_style):
    """Each answer is rank parity. Lookahead can persist, be discarded, or cost time."""
    count = len(colors)
    current = colors[i]
    first = (i + 1 + current) % count
    second = (first + colors[first] + 1) % count
    observed = {i, first, second}
    look = colors[second]
    first_state, marker = controller, memory
    if probe_style == 'retain':
        first_state = (controller + look) % 3
        marker |= 1 << ((current + look) % 5)
    elif probe_style == 'xor-register':
        first_state ^= look
    result = sum(u % 3 == current for u in range(i + 1)) % 2
    work = 2 + current + (look if probe_style == 'timing' else 0)
    return (first_state, marker, clock + work), observed, result


def before(colors, i, style):
    state = (0, 0, 0)
    for j in range(i):
        state, _, _ = panel_step(colors, j, *state, style)
    return state


def check_deferred_inputs():
    panels = 0
    for style in ('retain', 'discard', 'timing', 'xor-register'):
        for choices in product(range(3), repeat=5):
            for physical in (False, True):
                canonical = [0] * len(choices)
                sealed = set()
                stitched = (0, 0, 0)
                saved = []
                for i, choice in enumerate(choices):
                    alternatives = []
                    for color in range(3):
                        arr = canonical.copy()
                        arr[i] = color
                        alternatives.append(before(arr, i, style))
                    assert alternatives[0] == stitched
                    charge = i in sealed if physical else len(set(alternatives)) > 1
                    if not charge:
                        assert all(s == stitched for s in alternatives)
                        saved.append((i, stitched))
                        canonical[i] = choice
                    stitched, touched, _ = panel_step(canonical, i, *stitched, style)
                    sealed.update(j for j in touched if j > i)
                    panels += 1
                assert stitched == before(canonical, len(choices), style)
                for i, snapshot in saved:
                    for color in range(3):
                        trial = canonical[:i] + [color] + [0] * (len(choices) - i - 1)
                        assert before(trial, i, style) == snapshot
                        _, _, answer = panel_step(trial, i, *snapshot, style)
                        assert answer == sum(x % 3 == color for x in range(i + 1)) % 2
    return panels


def check_register_corrections():
    """The hypothetical prehistory may take a different time on each candidate."""
    checks = 0
    for colors in product(range(3), repeat=5):
        for style in ('xor-register', 'timing'):
            canonical = [0] * len(colors)
            stitched_clock = excess = 0
            memory = 0
            for i, choice in enumerate(colors):
                records = []
                for s in range(3):
                    candidate = canonical.copy()
                    candidate[i] = s
                    records.append(before(candidate, i, style))
                assert all(state[1] == memory for state in records)
                h = max(state[2] for state in records) - min(state[2] for state in records)
                correction = records[0][2] - records[choice][2]
                assert abs(correction) <= h
                canonical[i] = choice
                real_post, _, _ = panel_step(canonical, i, *records[choice], style)
                stitched_clock += real_post[2] - records[choice][2]
                excess += correction
                memory = real_post[1]
                assert stitched_clock == before(canonical, i + 1, style)[2] + excess
                checks += 1
    return checks


def check_colored_predecessor():
    """Reduce colored predecessor to parity of a rank on the flipped payloads."""
    queries = 0
    for h in (2, 3, 4):
        grid = list(product(range(2), range(h)))
        for keys in combinations(grid, h):
            for payloads in product(range(2), repeat=h):
                payload = dict(zip(keys, payloads))
                changes = {}
                previous = 0
                for key in keys:
                    changes[key] = previous ^ payload[key]
                    previous = payload[key]
                by_column = sorted(keys, key=lambda cell: (cell[1], cell[0]))
                colors = [row if changes[row, col] else 2 for row, col in by_column]
                for query in grid:
                    r, col = query
                    base = 0
                    expected = 0
                    for key in keys:
                        if key[0] < r:
                            base = payload[key]
                        if key <= query:
                            expected = payload[key]
                    date = sum(j <= col for _, j in by_column)
                    assert base ^ (colors[:date].count(r) % 2) == expected
                    queries += 1
    return queries


if __name__ == '__main__':
    print(f'{check_persistence()} historical cell values checked with four radix widths')
    print(f'{check_deferred_inputs()} panels checked across physical and semantic input completion')
    print(f'{check_register_corrections()} corrected boundary times and clock differences checked')
    print(f'{check_colored_predecessor()} colored-predecessor answers checked using one rank parity')
