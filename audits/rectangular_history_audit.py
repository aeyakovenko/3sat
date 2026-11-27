"""Compare compressed rectangle/XOR-diagonal history checks with direct evaluation."""

from collections import Counter, defaultdict
from dataclasses import dataclass
from itertools import product
from random import Random


@dataclass(frozen=True)
class Chart:
    # Each value is a packed vector of Boolean channel bits. Rectangles and
    # tracks contribute their masks by XOR, including when descriptors repeat.
    constant: int
    x_bits: tuple
    y_bits: tuple
    rectangles: tuple  # (x0, x1, y0, y1, mask)
    tracks: tuple      # (xor_offset, x0, x1, mask)


def linear(bits, x):
    result = 0
    for i, coefficient in enumerate(bits):
        if (x >> i) & 1:
            result ^= coefficient
    return result


def value(chart, x, y):
    answer = chart.constant ^ linear(chart.x_bits, x) ^ linear(chart.y_bits, y)
    for x0, x1, y0, y1, mask in chart.rectangles:
        if x0 <= x < x1 and y0 <= y < y1:
            answer ^= mask
    for offset, lo, hi, mask in chart.tracks:
        if lo <= x < hi and y == x ^ offset:
            answer ^= mask
    return answer


def dyadic_blocks(lo, hi):
    """Partition [lo,hi) into aligned power-of-two blocks."""
    while lo < hi:
        size = 1 << ((hi - lo).bit_length() - 1)
        if lo:
            size = min(size, lo & -lo)
        yield lo, size
        lo += size


def xor_intervals(lo, hi, mask):
    for start, size in dyadic_blocks(lo, hi):
        left = (start ^ mask) & -size
        yield left, left + size


def affine_histogram(bits, lo, hi, fixed, required):
    """Counts among x satisfying x & fixed == required, by value of L(x)."""
    result = Counter()
    for base, size in dyadic_blocks(lo, hi):
        if (base ^ required) & fixed & -size:
            continue
        low_fixed = required & (size - 1)
        hist = Counter({linear(bits, base | low_fixed): 1})
        for i in range(size.bit_length() - 1):
            if not ((fixed >> i) & 1):
                shifted = {a ^ bits[i]: count for a, count in hist.items()}
                hist.update(shifted)
        result.update(hist)
    return result


class BandTree:
    """Range XOR updates over y; each node holds a channel-value histogram."""

    def __init__(self, ends, bits, fixed, required):
        self.ends = ends
        self.position = {v: i for i, v in enumerate(ends)}
        self.hist = {}
        self.pending = defaultdict(int)

        def build(node, lo, hi):
            if hi == lo + 1:
                self.hist[node] = affine_histogram(bits, ends[lo], ends[hi], fixed, required)
                return
            mid = (lo + hi) // 2
            build(2*node, lo, mid)
            build(2*node + 1, mid, hi)
            self.combine(node)

        build(1, 0, len(ends) - 1)

    def combine(self, node):
        self.hist[node] = self.hist[2*node] + self.hist[2*node + 1]

    def shift(self, node, mask):
        if mask:
            self.hist[node] = Counter({x ^ mask: n for x, n in self.hist[node].items()})
            self.pending[node] ^= mask

    def toggle(self, y0, y1, mask):
        left, right = self.position[y0], self.position[y1]

        def update(node, lo, hi):
            if left >= hi or right <= lo:
                return
            if left <= lo and hi <= right:
                self.shift(node, mask)
                return
            mid = (lo + hi) // 2
            inherited = self.pending.pop(node, 0)
            self.shift(2*node, inherited)
            self.shift(2*node + 1, inherited)
            update(2*node, lo, mid)
            update(2*node + 1, mid, hi)
            self.combine(node)

        if left < right:
            update(1, 0, len(self.ends) - 1)


def toggle_interval(events, lo, hi, mask):
    if lo < hi:
        events[lo] ^= mask
        events[hi] ^= mask


def swept_histogram(chart, domain=(0, 0, 0, 0)):
    """x/y rectangle slabs plus separate one-dimensional diagonal corrections."""
    width = len(chart.x_bits)
    side = 1 << width
    fx, vx, fy, vy = domain
    changes = defaultdict(list)
    y_ends = {0, side}
    for x0, x1, y0, y1, mask in chart.rectangles:
        if x0 < x1 and y0 < y1:
            changes[x0].append((y0, y1, mask))
            changes[x1].append((y0, y1, mask))
            y_ends.update((y0, y1))
    y_tree = BandTree(sorted(y_ends), chart.y_bits, fy, vy)
    x_ends = sorted({0, side} | set(changes))
    result = Counter()
    for lo, hi in zip(x_ends, x_ends[1:]):
        for event in changes[lo]:
            y_tree.toggle(*event)
        hx = affine_histogram(chart.x_bits, lo, hi, fx, vx)
        for x_val, nx in hx.items():
            for y_val, ny in y_tree.hist[1].items():
                result[chart.constant ^ x_val ^ y_val] += nx * ny

    track_groups = defaultdict(list)
    for offset, lo, hi, mask in chart.tracks:
        track_groups[offset].append((lo, hi, mask))
    diagonal_bits = tuple(a ^ b for a, b in zip(chart.x_bits, chart.y_bits))
    for offset, tracks in track_groups.items():
        required_y_as_x = (vy ^ offset) & fy
        if (vx ^ required_y_as_x) & fx & fy:
            continue
        fixed = fx | fy
        required = vx | required_y_as_x
        base_events = defaultdict(int)
        track_events = defaultdict(int)
        for x0, x1, y0, y1, mask in chart.rectangles:
            for yl, yr in xor_intervals(y0, y1, offset):
                toggle_interval(base_events, max(x0, yl), min(x1, yr), mask)
        for lo, hi, mask in tracks:
            toggle_interval(track_events, lo, hi, mask)
        ends = sorted({0, side} | set(base_events) | set(track_events))
        base = chart.constant ^ linear(chart.y_bits, offset)
        correction = 0
        for lo, hi in zip(ends, ends[1:]):
            base ^= base_events[lo]
            correction ^= track_events[lo]
            if correction:
                for v, n in affine_histogram(diagonal_bits, lo, hi, fixed, required).items():
                    result[base ^ v] -= n
                    result[base ^ v ^ correction] += n
    assert all(n >= 0 for n in result.values())
    return +result


def brute_histogram(chart, domain=(0, 0, 0, 0)):
    side = 1 << len(chart.x_bits)
    fx, vx, fy, vy = domain
    return Counter(value(chart, x, y) for x in range(side) for y in range(side)
                   if x & fx == vx and y & fy == vy)


def xor_pullback(chart, a, b):
    rectangles = tuple(
        (xl, xr, yl, yr, mask)
        for x0, x1, y0, y1, mask in chart.rectangles
        for xl, xr in xor_intervals(x0, x1, a)
        for yl, yr in xor_intervals(y0, y1, b)
    )
    tracks = tuple(
        (offset ^ a ^ b, xl, xr, mask)
        for offset, lo, hi, mask in chart.tracks for xl, xr in xor_intervals(lo, hi, a)
    )
    constant = chart.constant ^ linear(chart.x_bits, a) ^ linear(chart.y_bits, b)
    return Chart(constant, chart.x_bits, chart.y_bits, rectangles, tracks)


def pack_scalar_charts(charts):
    width = len(charts[0].x_bits)
    constant = sum(c.constant << i for i, c in enumerate(charts))
    x_bits = tuple(sum(c.x_bits[k] << i for i, c in enumerate(charts)) for k in range(width))
    y_bits = tuple(sum(c.y_bits[k] << i for i, c in enumerate(charts)) for k in range(width))
    rectangles = tuple((*r[:-1], r[-1] << i) for i, c in enumerate(charts) for r in c.rectangles)
    tracks = tuple((*p[:-1], p[-1] << i) for i, c in enumerate(charts) for p in c.tracks)
    return Chart(constant, x_bits, y_bits, rectangles, tracks)


def successor_phases(width, include_wrap):
    """Within each phase of t=x*side+y, successor is XOR by a known mask."""
    both = 2 * width
    coord_mask = (1 << width) - 1
    for trailing_ones in range(both + int(include_wrap)):
        low = (1 << trailing_ones) - 1
        changed = (1 << min(trailing_ones + 1, both)) - 1
        domain = (changed >> width, low >> width, changed & coord_mask, low & coord_mask)
        yield changed >> width, changed & coord_mask, domain


def shear_chart(chart):
    """Express an ordered-prefix chart on (u,v)=(y,x XOR y) without tracks."""
    rectangles = []
    for x0, x1, y0, y1, mask in chart.rectangles:
        for x_start, x_size in dyadic_blocks(x0, x1):
            for y_start, y_size in dyadic_blocks(y0, y1):
                if x_size < y_size:
                    raise ValueError('y prefix must fix every high bit fixed by x')
                v_start = (x_start ^ y_start) & -x_size
                rectangles.append((y_start, y_start + y_size, v_start, v_start + x_size, mask))
    for offset, lo, hi, mask in chart.tracks:
        for ul, ur in xor_intervals(lo, hi, offset):
            rectangles.append((ul, ur, offset, offset + 1, mask))
    u_bits = tuple(a ^ b for a, b in zip(chart.x_bits, chart.y_bits))
    return Chart(chart.constant, u_bits, chart.x_bits, tuple(rectangles), ())


def shear_domain(domain):
    fx, vx, fy, vy = domain
    if fx & ~fy:
        raise ValueError('x-fixed bits require the corresponding y bits')
    return fy, vy, fx, (vx ^ vy) & fx


def ordered_prefix_chart(rng, width, channels):
    base = random_chart(rng, width, channels)
    rectangles = []
    for _ in range(7):
        # y's interval has at most as many free low bits as x's.
        free_x = rng.randrange(width + 1)
        free_y = rng.randrange(free_x + 1)
        x = rng.randrange(1 << (width - free_x)) << free_x
        y = rng.randrange(1 << (width - free_y)) << free_y
        rectangles.append((x, x + (1 << free_x), y, y + (1 << free_y),
                           rng.randrange(1 << channels)))
    return Chart(base.constant, base.x_bits, base.y_bits, tuple(rectangles), base.tracks)


def random_chart(rng, width, channels):
    side = 1 << width

    def interval():
        return sorted((rng.randrange(side + 1), rng.randrange(side + 1)))

    def mask():
        return rng.randrange(1 << channels)

    rectangles = [(*interval(), *interval(), mask()) for _ in range(rng.randrange(7))]
    tracks = [(rng.randrange(side), *interval(), mask()) for _ in range(rng.randrange(7))]
    if tracks and rng.randrange(2):
        tracks.extend([tracks[0]] * 2)
    if rectangles and rng.randrange(2):
        rectangles.extend([rectangles[0]] * 2)
    return Chart(mask(), tuple(mask() for _ in range(width)), tuple(mask() for _ in range(width)),
                 tuple(rectangles), tuple(tracks))


def main():
    # Exhaust all 4-by-4 axis intervals paired with one XOR track, including empties.
    intervals = [(l, r) for l in range(5) for r in range(l, 5)]
    pairs = 0
    for (x0, x1), (y0, y1), (lo, hi), offset in product(intervals, intervals, intervals, range(4)):
        chart = Chart(1, (1, 2), (2, 1), ((x0, x1, y0, y1, 1),), ((offset, lo, hi, 2),))
        assert swept_histogram(chart) == brute_histogram(chart)
        pairs += 1

    rng = Random(20261125)
    random_checks = 0
    pullbacks = 0
    for _ in range(90):
        width = rng.randrange(1, 6)
        side = 1 << width
        chart = random_chart(rng, width, 4)
        fx, fy = rng.randrange(side), rng.randrange(side)
        domain = (fx, rng.randrange(side) & fx, fy, rng.randrange(side) & fy)
        assert swept_histogram(chart, domain) == brute_histogram(chart, domain)
        random_checks += 1

        current, next_chart, addressed = [random_chart(rng, width, 1) for _ in range(3)]
        a, b = rng.randrange(side), rng.randrange(side)
        address_pullback = xor_pullback(addressed, a, b)
        for wrap in [False, True]:
            combined = Counter()
            for dx, dy, phase in successor_phases(width, wrap):
                fields = pack_scalar_charts((current, xor_pullback(next_chart, dx, dy), address_pullback))
                combined.update(swept_histogram(fields, phase))
            direct = Counter()
            for t in range(side*side if wrap else side*side - 1):
                x, y = divmod(t, side)
                nx, ny = divmod((t+1) % (side*side), side)
                direct[value(current, x, y) | (value(next_chart, nx, ny) << 1) |
                       (value(addressed, x ^ a, y ^ b) << 2)] += 1
            # Exact histograms imply equal violation counts for every 3-input gate predicate.
            assert combined == direct
            pullbacks += 1

    shear_points = 0
    sheared_gates = 0
    for _ in range(60):
        width = rng.randrange(1, 6)
        side = 1 << width
        ordered = ordered_prefix_chart(rng, width, 4)
        sheared = shear_chart(ordered)
        assert not sheared.tracks
        for x, y in product(range(side), repeat=2):
            assert value(ordered, x, y) == value(sheared, y, x ^ y)
            shear_points += 1

        current, next_chart, addressed = [ordered_prefix_chart(rng, width, 1) for _ in range(3)]
        a, b = rng.randrange(side), rng.randrange(side)
        address_pullback = xor_pullback(addressed, a, b)
        for wrap in [False, True]:
            combined = Counter()
            for dx, dy, phase in successor_phases(width, wrap):
                if dx:  # A carry entering x forces all low-half bits to one.
                    assert phase[2:] == (side-1, side-1)
                fields = pack_scalar_charts((current, xor_pullback(next_chart, dx, dy), address_pullback))
                transformed = shear_chart(fields)
                assert not transformed.tracks
                combined.update(swept_histogram(transformed, shear_domain(phase)))
            direct = Counter()
            for t in range(side*side if wrap else side*side - 1):
                x, y = divmod(t, side)
                nx, ny = divmod((t+1) % (side*side), side)
                direct[value(current, x, y) | (value(next_chart, nx, ny) << 1) |
                       (value(addressed, x ^ a, y ^ b) << 2)] += 1
            assert combined == direct
            sheared_gates += 1

    # A single equality track represents the identity matrix. Each row has its
    # own pivot; its GF(2) rank equals the side. Also count a grid too large to scan.
    identity_width = 7
    side = 1 << identity_width
    identity = Chart(0, (0,)*identity_width, (0,)*identity_width, (), ((0, 0, side, 1),))
    rows = [sum(value(identity, x, y) << y for y in range(side)) for x in range(side)]
    assert rows == [1 << x for x in range(side)]
    huge_side = 1 << 40
    huge = Chart(0, (0,)*40, (0,)*40, (), ((0, 0, huge_side, 1),))
    assert swept_histogram(huge) == {0: huge_side**2 - huge_side, 1: huge_side}
    print(f'{pairs} rectangle/track pairs, {random_checks} restricted charts and '
          f'{pullbacks} successor/XOR gate histograms matched direct counts; '
          f'{shear_points} pointwise shears and {sheared_gates} track-free successor/XOR '
          f'gate histograms matched; '
          f'one track had rank {side} and the 2^80-cell identity count was exact.')


if __name__ == '__main__':
    main()
