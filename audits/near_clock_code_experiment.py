"""Finite exact-arithmetic checks of nearby-clock batch prefix coding."""

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Callable


def ceiling(x):
    return -(-x.numerator // x.denominator)


def first_cell(lo, depth):
    return ceiling(lo * (1 << depth))


@dataclass
class Batch:
    start: Fraction
    stop: Fraction
    depth: int
    lookup: Callable[[int], str | None]
    # Expected names, independently enumerated for the finite experiment.
    codes: list[tuple[int, str]]


def exact_batch(start, d, words):
    width = Fraction(1, 1 << (d + 2))
    depth = d + 3
    stop = start + len(words) * width

    def lookup(index):
        left = Fraction(index, 1 << depth)
        if not start <= left < stop:
            return None
        rank = (left - start) // width
        return words[rank] if index == first_cell(start + rank * width, depth) else None

    codes = []
    for rank, word in enumerate(words):
        lo = start + rank * width
        index = first_cell(lo, depth)
        assert lo <= Fraction(index, 1 << depth)
        assert Fraction(index + 1, 1 << depth) <= lo + width
        codes.append((index, word))
    return Batch(start, stop, depth, lookup, codes)


def approximate_batch(start, d, height, words, upper):
    """Use exact rational child shares of independently approximated counts."""
    unit = Fraction(1, 1 << (d + 4))
    depth = d + 6
    stop = start + upper.get("", 0) * unit

    def lookup(index):
        point = Fraction(index, 1 << depth)
        if not start <= point < stop:
            return None
        prefix = ""
        lo, hi = start, stop
        while len(prefix) < height:
            left = upper.get(prefix + "0", 0)
            right = upper.get(prefix + "1", 0)
            assert left + right > 0
            cut = lo + (hi - lo) * left / (left + right)
            if point < cut:
                prefix += "0"
                hi = cut
            else:
                prefix += "1"
                lo = cut
        return prefix if index == first_cell(lo, depth) else None

    # Compute widths independently as root width times the path product.
    # The lookup above does not enumerate descendants.
    cursor = start
    codes = []
    for word in sorted(words):
        width = stop - start
        prefix = ""
        for bit in word:
            denominator = upper.get(prefix + "0", 0) + upper.get(prefix + "1", 0)
            prefix += bit
            width *= upper[prefix] / denominator
        assert unit / 2 <= width <= 4 * unit
        index = first_cell(cursor, depth)
        assert cursor <= Fraction(index, 1 << depth)
        assert Fraction(index + 1, 1 << depth) <= cursor + width
        codes.append((index, word))
        cursor += width
    assert cursor == stop
    return Batch(start, stop, depth, lookup, codes)


def decode(bits, batches):
    index = used = 0
    left, right = Fraction(0), Fraction(1)
    for batch in batches:
        if batch.start == batch.stop:
            continue
        while left < batch.stop and batch.start < right:
            if used >= batch.depth:
                word = batch.lookup(index >> (used - batch.depth))
                if word is not None:
                    return word, used
                break
            assert used < len(bits), "decoder read beyond the exact name"
            index = 2 * index + int(bits[used])
            used += 1
            left, right = Fraction(index, 1 << used), Fraction(index + 1, 1 << used)
    return None, used


def check_streams(batches, all_gaps=False):
    names = {}
    deeper_before = 0
    deepest = 0
    for batch in batches:
        for index, word in batch.codes:
            assert 0 <= index < (1 << batch.depth)
            code = format(index, f"0{batch.depth}b")
            assert code not in names
            names[code] = word
            deeper_before += deepest > batch.depth
            # On the exact name even an attempted additional read fails.
            assert decode(code, batches) == (word, len(code))
            assert decode(code + "10110", batches) == (word, len(code))
        if batch.codes:
            deepest = max(deepest, batch.depth)
    ordered = sorted(names)
    assert all(not later.startswith(earlier) for earlier, later in zip(ordered, ordered[1:]))
    gap_count = 0
    if all_gaps:
        for digits in product("01", repeat=deepest):
            sample = "".join(digits)
            hits = [name for name in names if sample.startswith(name)]
            result, consumed = decode(sample, batches)
            if hits:
                assert len(hits) == 1
                assert (result, consumed) == (names[hits[0]], len(hits[0]))
            else:
                assert result is None
                gap_count += 1
    return len(names), deeper_before, gap_count


def exact_layouts():
    layouts = names = decreasing = gaps = 0
    choices = list(product(range(4), range(3)))
    for specs in product(choices, repeat=3):
        cursor = Fraction(0)
        batches = []
        for number, (d, count) in enumerate(specs):
            words = [str((number, rank)) for rank in range(count)]
            batch = exact_batch(cursor, d, words)
            batches.append(batch)
            cursor = batch.stop
        if cursor > 1:
            continue
        n, earlier, unused = check_streams(batches, all_gaps=True)
        layouts += 1
        names += n
        decreasing += earlier
        gaps += unused
    return layouts, names, decreasing, gaps


def epoch_histories():
    words = ("0", "10")
    true = ((Fraction(1, 8), Fraction(1, 16)),
            (Fraction(1, 4), Fraction(1, 8)),
            (Fraction(1, 4), Fraction(1, 4)))
    histories = names = fluctuating = 0
    for divisors in product((1, 4, 32), repeat=6):
        estimates = [[true[q][i] / divisors[2*q+i] for i in range(2)] for q in range(3)]
        fluctuating += any(estimates[q][i] > estimates[q+1][i]
                           for q in range(2) for i in range(2))
        first = {}
        cursor = Fraction(0)
        batches = []
        for q in range(1, 4):
            for d in range(2*q + 3):
                new_words = []
                for i, word in enumerate(words):
                    eligible = len(word) <= q and estimates[q-1][i] >= Fraction(1, 1 << d)
                    if eligible and (word, d) not in first:
                        first[word, d] = q
                        new_words.append(word)
                batch = exact_batch(cursor, d, new_words)
                batches.append(batch)
                cursor = batch.stop
        assert cursor <= sum(true[-1]) / 2
        for i, word in enumerate(words):
            for d in range(9):
                possible = [q for q in range(1, 4) if len(word) <= q and d <= 2*q+2
                            and estimates[q-1][i] >= Fraction(1, 1 << d)]
                assert first.get((word, d)) == (min(possible) if possible else None)
        counts = check_streams(batches)
        names += counts[0]
        histories += 1
    return histories, fluctuating, names


def approximate_layouts():
    cases = names = decreasing = narrowed = unused = 0
    for height in (2, 3):
        universe = ["".join(bits) for bits in product("01", repeat=height)]
        for mask in range(1 << len(universe)):
            words = [word for i, word in enumerate(universe) if mask & (1 << i)]
            counts = {}
            for word in words:
                for k in range(height + 1):
                    prefix = word[:k]
                    counts[prefix] = counts.get(prefix, 0) + 1
            prefixes = sorted(counts)
            if height == 2:
                ratios = (Fraction(1), Fraction(5, 4), Fraction(11, 8))
                profiles = product(ratios, repeat=len(prefixes))
            else:
                ratios = (Fraction(1), Fraction(9, 8), Fraction(5, 4))
                # All supports, exact and extremal or alternating perturbations.
                profiles = [tuple(ratios[(a*j+b) % 3] for j in range(len(prefixes)))
                            for a, b in product(range(3), repeat=2)]
            assert all(1 <= value and value**height <= 2 for value in ratios)
            for profile in profiles:
                upper = {prefix: counts[prefix] * ratio for prefix, ratio in zip(prefixes, profile)}
                before = exact_batch(Fraction(0), 6, ["first"])
                main = approximate_batch(before.stop, 1, height, words, upper)
                after = exact_batch(main.stop, 0, ["last"])
                assert after.stop <= 1
                n, earlier, _ = check_streams([before, main, after])
                oracle = dict(main.codes)
                for index in range(1 << main.depth):
                    assert main.lookup(index) == oracle.get(index)
                narrowed += len(oracle)
                unused += (1 << main.depth) - len(oracle)
                cases += 1
                names += n
                decreasing += earlier
    return cases, names, decreasing, narrowed, unused


if __name__ == "__main__":
    cases, names, decreasing, gaps = exact_layouts()
    print(f"Exact batches: {cases} layouts, {names} names, {decreasing} names after "
          f"deeper batches, {gaps} unused full-grid addresses.", flush=True)
    cases, fluctuating, names = epoch_histories()
    print(f"Epoch requests: {cases} histories, {fluctuating} with a downward estimate, "
          f"{names} names.", flush=True)
    cases, names, decreasing, leaves, unused = approximate_layouts()
    print(f"Rational subdivision: {cases} support/estimate profiles, {leaves} adaptive "
          f"leaf addresses, {names} names including neighbors, {decreasing} names "
          f"after a deeper batch, {unused} unused adaptive-grid addresses.", flush=True)
