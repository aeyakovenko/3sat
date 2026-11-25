"""Check the obstruction for first-produced addresses in finite word models."""

from itertools import product

from homogeneous_ram_word_clock_audit import TAIL, encode, entails_sat


SWAPPED_TAIL = b"2 1 3 0\n"


def check_dimacs_edits():
    files = 0
    for width_bytes in (10, 12, 16, 32):
        for switches in product((False, True), repeat=7):
            edits = {i for i, switch in enumerate(switches) if switch}
            original_layout = encode(width_bytes, 7, edits)
            assert original_layout.count(TAIL) == 8
            swapped = original_layout.replace(TAIL, SWAPPED_TAIL)
            assert entails_sat(swapped) == (not edits)
            files += 1
    return files


def rotate(x, distance, width):
    shift = distance % width
    mask = (1 << width) - 1
    return ((x << shift) | (x >> (width - shift))) & mask


def possible_values(a, y, width):
    q = 1 << width
    mask = q - 1
    yield from (a+y, a-y, y-a, a*y, 0, 1)
    for table in range(16):
        result = 0
        for k, lane in enumerate((~a & ~y, ~a & y, a & ~y, a & y)):
            if table >> k & 1:
                result |= lane
        yield result
    for v, count in ((a, y), (y, a)):
        for shift in {min(width, count), count % width}:
            yield v << shift
            yield v >> shift
        yield rotate(v, count, width)
        yield rotate(v, -count, width)


def check(width, length, a):
    q = 1 << width
    mask = q-1
    assert (a & 3) == 2 and q//8 < a < q//4 and length < q//8
    candidates = {p for p in range((length+1)//2, length) if p % 4 == 3}
    by_rotation = set()
    for direction in (-1, 1):
        dist = (direction * a) % width
        if not dist:
            continue
        for p in candidates:
            if rotate(p, -dist, width) < length:
                by_rotation.add(p)
    b = (length-1).bit_length()
    k = width-b
    assert len(by_rotation) <= (2 * (1 << max(0, b-k)))
    # Operations on A shifted by a varying word are handled as a small exception set.
    small_image = {0, 1}
    for j in range(width+1):
        small_image.update(((a << j) & mask, a >> j, rotate(a,j,width), rotate(a,-j,width)))
    claimed = candidates - by_rotation - small_image
    actual = set(candidates)
    for y in range(length):
        for output in possible_values(a,y,width):
            p = output & mask
            if p != y:
                actual.discard(p)
    assert claimed <= actual
    return len(candidates), len(claimed), len(actual)


if __name__ == "__main__":
    samples = 0
    total = [0, 0, 0]
    for w in (16, 24, 32, 80, 96, 128):
        prefixes = (0x32, 0x72) if w == 16 else (0x32, 0x7132)
        raw_words = [(0x2d << (w-8)) + prefix for prefix in prefixes]
        if w >= 80:
            body = SWAPPED_TAIL.ljust(w//8 - 1, b' ') + b'-'
            raw_words.append(int.from_bytes(body, 'little'))
        for a in raw_words:
            for length in (211, 517, 1093, 2137, 4096):
                counts = check(w, length, a)
                total = [s+t for s, t in zip(total, counts)]
                samples += 1
    print(samples, "address intervals and raw words checked; candidates, certified, actual:", total)
    print(check_dimacs_edits(), "proper DIMACS files checked with the swapped tail")
