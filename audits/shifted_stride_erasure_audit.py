"""Replay signed-stride crossed scans, including all scratch reads and writes."""

from bisect import bisect_right
from itertools import product

from erased_shifted_signs_audit import direct_sat, normalized, observe_pass
from shifted_dimacs_scan_wave_audit import Memory


def file_layout(width, stride, start, a, b):
    size = 1 << width
    file_words = size // (2 * width)
    assert 16 * (((file_words * width + 1).bit_length() + 15) // 16) == width
    word_bytes = width // 8
    blank = b' ' * word_bytes
    span = 44 * abs(stride) + 4
    low = 64 if not 62 <= start <= 66 + span else 66 + span + 32
    first = low + (abs(stride) if stride > 0 else 41 * abs(stride))
    sites = [first + 8 * i * stride for i in range(6)]
    assert max(sites) + abs(stride) + 1 < file_words
    assert not min(sites + [first - stride]) <= start <= max(sites + [first - stride])
    clauses = [(-var, sign6 * 6, sign7 * 7) for var in (2, 3)
               for sign6, sign7 in product((-1, 1), repeat=2)]
    prefix = b'p cnf 7 14\n' + b''.join(
        (' '.join(map(str, clause)) + ' 0\n').encode() for clause in clauses)
    assert len(prefix) < word_bytes
    words = {0: prefix.ljust(word_bytes)}
    for i, (site, name, bit) in enumerate(zip(sites, (1, 4, 5, 1, 4, 5), (a, 0, 1, b, 0, 1))):
        words[site] = blank[:-1] + (b'-' if bit else b' ')
        suffix = f'{name} 2 3 0\n'.encode()
        words[site + 1] = suffix.ljust(word_bytes)
        if i in (0, 3):
            anchor = site - stride
            tag = b'\t' if i == 0 else b'\n'
            if anchor == site + 1:
                words[anchor] = (suffix + tag).ljust(word_bytes - 1) + b'\n'
            else:
                words[anchor] = tag + blank[1:-1] + b'\n'
    raw = b''.join(words.get(i, blank) for i in range(max(words) + 1))
    assert direct_sat(raw) == (a == b)
    original = {i: int.from_bytes(v, 'little') for i, v in words.items()}
    blank_value = int.from_bytes(blank, 'little')
    for site in (sites[0], sites[3]):
        marker = original[site - stride]
        assert marker != blank_value and list(original.values()).count(marker) == 1
    assert min(original.values()) > file_words
    boundaries = {0, file_words}
    for i in words:
        boundaries.update((i, i + 1))
    runs = normalized((i, original.get(i, blank_value) if i < file_words else 0)
                      for i in sorted(boundaries))
    return runs, (sites[0], sites[3]), (sites[2], sites[5])


def conjugate(size, physical, start, stride):
    """Conjugate both the address and the stored pointer to lap coordinates."""
    inverse = pow(stride, -1, size)
    cuts = {0}
    for boundary, _ in physical:
        for wrap in range(-abs(stride) - 1, abs(stride) + 2):
            threshold = boundary + wrap * size - start
            if stride > 0:
                cut = -((-threshold) // stride)
            else:
                cut = threshold // stride + 1
            if 0 < cut < size:
                cuts.add(cut)
    starts = [i for i, _ in physical]
    data = []
    for j in sorted(cuts):
        address = (start + j * stride) % size
        value = physical[bisect_right(starts, address) - 1][1]
        data.append((j, ((value - start) * inverse) % size))
    return Memory(size, normalized(data))


def check_small_conjugation():
    cases = 0
    for size in (4, 8, 16, 32):
        for stride, start, seed in product((-5, -3, -1, 1, 3, 5), range(size), range(4)):
            raw = [((i // (seed + 1)) ** 2 + 3 * seed) % size for i in range(size)]
            mem = conjugate(size, normalized(enumerate(raw)), start, stride)
            for _ in range(2):
                expected = []
                for j in range(size):
                    p = (start + j * stride) % size
                    dest = raw[p]
                    expected.append(((dest - start) * pow(stride, -1, size)) % size)
                    raw[dest] = (p + stride) % size
                assert observe_pass(mem) == normalized(enumerate(expected))
                assert tuple(mem.runs()) == tuple(conjugate(
                    size, normalized(enumerate(raw)), start, stride).runs())
            cases += 1
    return cases


def check_case(width, stride, start):
    size = 1 << width
    traces = [[], []]
    ends = [[], []]
    labels = list(product((0, 1), repeat=2))
    for a, b in labels:
        runs, private, _ = file_layout(width, stride, start, a, b)
        mem = conjugate(size, runs, start, stride)
        original = Memory(size, [(j, value) for j, _, value in mem.runs()])
        for lap in range(2):
            reads = Memory(size, observe_pass(mem))
            if lap == 0:
                for site in private:
                    for offset in (0, 8, 16):
                        j = ((site + offset * stride - start) * pow(stride, -1, size)) % size
                        assert reads.interval(j)[0] == original.interval(j)[0]
            traces[lap].append(reads)
            ends[lap].append(tuple(mem.runs()))
    private_times = {((i - start) * pow(stride, -1, size)) % size: bit
                     for bit, i in enumerate(private)}
    first_boundary = [Memory(size, [(j, value) for j, _, value in e]) for e in ends[0]]
    for observations in [*traces, first_boundary]:
        cuts = sorted(set().union(*(trace.start for trace in observations),
                                  private_times, {j + 1 for j in private_times if j + 1 < size}))
        for j in cuts:
            values = [trace.interval(j)[0] for trace in observations]
            if len(set(values)) == 1:
                continue
            assert j in private_times, (width, stride, start, j, 'private value off site')
            bit = private_times[j]
            assert all(values[i] == values[k] for i in range(4) for k in range(4)
                       if labels[i][bit] == labels[k][bit])
    assert all(e == ends[1][0] for e in ends[1])
    assert len({trace.interval(size - 1)[0] for trace in traces[1]}) == 1
    return all(e == ends[0][0] for e in ends[0])


def starts_for(width, stride):
    size = 1 << width
    runs, sites, _ = file_layout(width, stride, 0, 0, 0)
    original = dict(runs)
    markers = [original[i - stride] for i in sites]
    blank = b' ' * (width // 8)
    hubs = [int.from_bytes(blank[:-1] + tail, 'little') for tail in (b' ', b'-')]
    return {0, 1, 63, 64, sites[0], sites[1], size // (2 * width) - 1,
            size // 2, size - 1, *(v + delta * stride for v in markers + hubs
                                    for delta in (-1, 0, 1))}


if __name__ == '__main__':
    print(f'{check_small_conjugation()} direct two-lap small-memory comparisons')
    cases = merged_first = 0
    for width, stride in product((1024, 1536), (-5, -3, -1, 1, 3, 5)):
        for start in sorted(starts_for(width, stride)):
            merged_first += check_case(width, stride, start)
            cases += 1
    print(f'{cases} signed-stride/start/width cases on four proper DIMACS files each')
    print(f'{merged_first} first-lap coalescences, {cases} second-lap coalescences')
