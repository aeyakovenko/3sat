"""Check the guard layout, read consistency, opposite verdicts, and encoded witnesses."""

from collections import Counter
from itertools import combinations_with_replacement, permutations, product
from math import comb, factorial


def encode_clause(clause, width):
    return ''.join(str(int(v < 0)) + format(abs(v), f'0{width - 1}b') for v in clause)


def unit(v):
    return (v, v, v)


def tautology(v):
    return (v, -v, v)


def path_clauses(count):
    inner = [(-i, i + 1, i + 1) for i in range(1, count - 1)]
    return [unit(1), *inner, unit(1 - count)]


def accepted(clauses, mask):
    return all(any(bool(mask >> (abs(v) - 1) & 1) != (v < 0) for v in clause)
               for clause in clauses)


def layout(width, header, logical):
    word = 12 * width
    stride = 3 * width
    start = (len(header) + word - 1) // word * word
    guard_index, phase = divmod(start - len(header), stride)
    count = len(logical)
    guard = tautology(2 ** (width - 1) - 1)
    clauses = [guard] * (4 * count + 9)
    for source, clause in enumerate(logical):
        index = guard_index + 4 * source
        clauses[index + 1:index + 4] = [
            clause, tautology(2 ** (width - 2) + source), tautology(1)]
    body = header + ''.join(encode_clause(c, width) for c in clauses)
    return body, start, phase


def check_alignment(width, header, logical):
    bits, start, phase = layout(width, header, logical)
    count = len(logical)
    word, stride = 12 * width, 3 * width
    words = [bits[start + j * word:start + (j + 1) * word] for j in range(count)]
    assert len(set(words)) == count
    for i, raw in enumerate(words):
        tag_position = 2 * stride - phase
        tag = int(raw[tag_position + 1:tag_position + width], 2)
        assert tag - 2 ** (width - 2) == i

    order = list(reversed(range(count)))
    changed = bits[:start] + ''.join(words[i] for i in order) + bits[start + count * word:]
    expected, _, _ = layout(width, header, [logical[i] for i in order])
    # layout() numbers source tags afresh. Compare the logical, filler and guard clauses.
    for index in range((len(bits) - len(header)) // stride):
        pos = len(header) + index * stride
        if any(start + (j + 1) * word - 2 * stride - phase == pos for j in range(count)):
            continue
        assert changed[pos:pos + stride] == expected[pos:pos + stride]
    return words


def check_read_extensions():
    tested = 0
    for count in range(1, 5):
        orders = list(permutations(range(count)))
        pairs = list(product(range(count), repeat=2))
        for observations in combinations_with_replacement(pairs, 3):
            loc = dict(observations)
            src = dict((s, p) for p, s in observations)
            local = len(set(observations)) == len(loc) == len(src)
            full = any(all(order[p] == s for p, s in observations) for order in orders)
            assert local == full
            tested += 1
    return tested


def check_sensitivity():
    tested = 0
    for count in range(2, 9):
        yes, no = [unit(1)] * count, path_clauses(count)
        assert accepted(yes, 1)
        assert all(not accepted(no, v) for v in range(1 << (count - 1)))
        for i in range(count):
            flip_yes = yes.copy()
            flip_no = no.copy()
            flip_yes[i] = unit(-1)
            flip_no[i] = tautology(1)
            assert not any(accepted(flip_yes, v) for v in (0, 1))
            assert any(accepted(flip_no, v) for v in range(1 << (count - 1)))
            tested += 2
    return tested


def check_encoded_assignments():
    tested = 0
    for count in range(2, 9):
        count_by_bits = {}
        tracked = range(count // 2)
        for order in permutations(range(count)):
            pattern = tuple(order[2 * v] % 2 for v in tracked)
            count_by_bits[pattern] = count_by_bits.get(pattern, 0) + 1
        for pattern in product((0, 1), repeat=count // 2):
            encoded = list(range(count))
            for v in tracked:
                if pattern[v]:
                    encoded[2 * v], encoded[2 * v + 1] = encoded[2 * v + 1], encoded[2 * v]
            assert tuple(encoded[2 * v] % 2 for v in tracked) == pattern
            assert count_by_bits[pattern] * 2 ** count >= factorial(count)
            tested += 1
    return tested


def check_adaptive_discoveries():
    total = 0
    for count in range(2, 9):
        histogram = Counter()
        for order in permutations(range(count)):
            positions = list(range(count))
            unused = list(positions)
            state = 1
            hits = 0
            while positions:
                pos = positions.pop(state % len(positions))
                guess = unused[(state * 3 + pos) % len(unused)]
                tag = order[pos]
                hits += guess == tag
                unused.remove(tag)
                state = (state * 5 + tag + pos) % (count + 1)
            histogram[hits] += 1
        weighted = sum(frequency * count ** hits for hits, frequency in histogram.items())
        assert weighted == factorial(count) * comb(2 * count - 1, count)
        total += factorial(count)
    return total


def check_lengths():
    tested = 0
    for width in range(11, 31):
        count = 2 ** width // (16 * width)
        for header in range(1, 5 * width):
            length = header + (4 * count + 9) * 3 * width
            assert (length + 1).bit_length() == width
            tested += 1
    return tested


if __name__ == '__main__':
    layouts = 0
    for width in range(6, 10):
        for offset in range(12 * width):
            for clauses in ([unit(1)] * 5, path_clauses(5)):
                check_alignment(width, '0' * (12 * width + offset), clauses)
                layouts += 1
    print(f'{layouts} physical layouts and {check_lengths()} header/width choices checked')
    print(f'{check_read_extensions()} read histories and {check_sensitivity()} opposite-verdict edits checked')
    print(f'{check_encoded_assignments()} parity patterns recover their truth assignments')
    print(f'{check_adaptive_discoveries()} adaptive word orders matched the exact guessing moment')
