"""Exercise exact minority-bit retrieval when membership of a queried key is promised."""

from itertools import product
from math import ceil, log2
import random


def multiply(left, right, bits, modulus):
    result = 0
    while right:
        if right & 1:
            result ^= left
        right >>= 1
        left <<= 1
        if left >> bits:
            left ^= modulus
    return result


def hash_rows(bits, modulus):
    size = 1 << bits
    return [[multiply(key, seed, bits, modulus) for key in range(size)]
            for seed in range(size)]


def separate(target, opposite, rows):
    size = 1 << (2 * len(target) - 1).bit_length()
    trials = ceil(log2(2 + 2 * len(opposite) / len(target)))
    assert size <= len(rows)
    arrays = []
    survivors = opposite
    for _ in range(trials):
        # Conditional averaging permits fixing each hash in turn. Choose the
        # largest allowed survivor set to exercise later levels of the cascade.
        chosen = None
        for seed, row in enumerate(rows):
            marked = {row[key] % size for key in target}
            remaining = {key for key in survivors if row[key] % size in marked}
            if 2 * len(remaining) <= len(survivors):
                if chosen is None or len(remaining) > len(chosen[2]):
                    chosen = (seed, marked, remaining)
                if 2 * len(remaining) >= len(survivors) - 1:
                    break
        assert chosen is not None
        seed, marked, survivors = chosen
        arrays.append((seed, marked))
    assert 2 * len(survivors) <= len(target)
    return size, arrays, survivors


def encode(labels, rows):
    ones = {key for key, label in labels.items() if label}
    zeros = set(labels) - ones
    target_bit = len(ones) <= len(zeros)
    target, opposite = (ones, zeros) if target_bit else (zeros, ones)
    minority = len(target)
    layers = []
    space = 0
    while target:
        size, arrays, survivors = separate(target, opposite, rows)
        layers.append((size, arrays))
        space += size * len(arrays)
        opposite, target = target, survivors

    def lookup(key):
        wanted = target_bit
        for size, arrays in layers:
            if any(rows[seed][key] % size not in marked for seed, marked in arrays):
                return not wanted
            wanted = not wanted
        return not wanted

    return lookup, len(layers), space, minority


def check(labels, rows):
    lookup, depth, space, minority = encode(labels, rows)
    assert all(lookup(key) == bit for key, bit in labels.items())
    assert depth <= minority.bit_length()
    if minority:
        assert space <= 12 * minority * log2(2 * len(labels) / minority) + 32 * minority
    else:
        assert space == 0
    return depth


def weighted_entropy(counts):
    total = sum(counts)
    return total * log2(total) - sum(n * log2(n) for n in counts) if total else 0


def shared_bank_lookup(labels, rows, bank):
    classes = [{key for key, label in labels.items() if label == bit} for bit in (0, 1)]
    wanted = int(len(classes[1]) <= len(classes[0]))
    minority, other = classes[wanted], classes[1 - wanted]
    if not minority:
        return lambda key: 1 - wanted

    for schedule in bank:
        cap = 1 << (len(minority) - 1).bit_length()
        target, opposite = minority, other
        stages = []
        for j in range(cap.bit_length()):
            slots = 2 * cap
            trials = ceil(log2(16 + 16 * len(other) / cap)) if j == 0 else ceil(log2(32 * (j + 1)**2))
            assert trials <= len(schedule[j])
            arrays = [(seed, {rows[seed][key] % slots for key in target})
                      for seed in schedule[j][:trials]]
            survivors = {key for key in opposite
                         if all(rows[seed][key] % slots in marks for seed, marks in arrays)}
            if 2 * len(survivors) > cap:
                break
            stages.append((slots, arrays))
            opposite, target = target, survivors
            cap //= 2
        else:
            assert not target and cap == 0
            def lookup(key):
                polarity = wanted
                for slots, arrays in stages:
                    if any(rows[seed][key] % slots not in marks for seed, marks in arrays):
                        return 1 - polarity
                    polarity = 1 - polarity
                return 1 - polarity

            return lookup
    raise AssertionError("finite seed bank had no successful schedule")


def check_words(words, rows, bank=None):
    def build(keys):
        masks = {words[key] for key in keys}
        if len(masks) == 1:
            return masks.pop(), 0, 0
        # The highest varying bit supplies the compressed trie split.
        bit = (min(masks) ^ max(masks)).bit_length() - 1
        labels = {key: (words[key] >> bit) & 1 for key in keys}
        if bank is None:
            lookup, _, _, _ = encode(labels, rows)
        else:
            lookup = shared_bank_lookup(labels, rows, bank)
        parts = [[key for key in keys if labels[key] == value] for value in (0, 1)]
        zero, zero_entropy, zero_count = build(parts[0])
        one, one_entropy, one_count = build(parts[1])
        entropy = weighted_entropy([len(part) for part in parts])
        return (lookup, (zero, one)), zero_entropy + one_entropy + entropy, 1 + zero_count + one_count

    root, entropy_sum, branch_count = build(list(words))
    counts = {}
    for key, mask in words.items():
        node = root
        while isinstance(node, tuple):
            lookup, children = node
            node = children[lookup(key)]
        assert node == mask
        counts[mask] = counts.get(mask, 0) + 1
    assert branch_count == len(counts) - 1
    assert abs(entropy_sum - weighted_entropy(counts.values())) < 1e-8
    return entropy_sum


def main():
    small_rows = hash_rows(3, 0b1011)
    for labels in product((None, 0, 1), repeat=8):
        check({key: bit for key, bit in enumerate(labels) if bit is not None}, small_rows)
    rows = hash_rows(8, 0x11B)
    for nonzero_seed in rows[1:]:
        assert len(set(nonzero_seed)) == 256
    rng = random.Random(1795550838)
    depths = []
    for _ in range(128):
        count = rng.randrange(8, 180)
        keys = rng.sample(range(256), count)
        cut = rng.randrange(count + 1)
        depths.append(check({key: index < cut for index, key in enumerate(keys)}, rows))
    for masks in product(range(4), repeat=4):
        check_words(dict(zip((1, 2, 5, 7), masks)), small_rows)
    for _ in range(48):
        masks = rng.sample(range(256), rng.randrange(1, 12))
        keys = rng.sample(range(256), rng.randrange(12, 96))
        check_words({key: rng.choice(masks) for key in keys}, rows)
    for trial in range(204):
        keys = rng.sample(range(256), rng.randrange(32, 230))
        masks = rng.sample(range(256), rng.randrange(2, 58))
        words = {key: rng.choice(masks) for key in keys}
        count = ceil(log2(4 * (1 + len(set(words.values())))))
        bank = [[[rng.randrange(256) for _ in range(20)] for _ in range(10)]
                for _ in range(count)]
        check_words(words, rows, bank)
        groups = {}
        for key, mask in words.items():
            tag = key % (1 + trial % 17)
            groups.setdefault(tag, {})[key] = mask
        conditional = sum(check_words(group, rows, bank) for group in groups.values())
        for threshold in (2, 4, 8, 16):
            symbols = sum(len(set(group.values())) for group in groups.values())
            bound = len(groups) * threshold + len(groups) + conditional / log2(threshold)
            assert symbols <= bound + 1e-8
    assert max(depths) >= 3
    print(f'{3**8:,} partial labelings and {len(depths)} seeded examples passed; '
          f'maximum {max(depths)} nonempty cascade levels. 304 word tries, 204 shared-bank '
          f'tries, and 204 tagged forests passed.')


if __name__ == '__main__':
    main()
