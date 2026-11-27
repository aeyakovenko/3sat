"""Finite checks of first-departure pins, block-local edit balls and shared linear tags."""

from collections import defaultdict
from itertools import product


def distance(left, right):
    costs = list(range(len(right) + 1))
    for i, a in enumerate(left, 1):
        updated = [i]
        for j, b in enumerate(right, 1):
            updated.append(min(updated[-1] + 1, costs[j] + 1, costs[j-1] + (a != b)))
        costs = updated
    return costs[-1]


def run_block(program, initial, controller):
    """Each small native instruction performs a fixed or register-indexed load or store."""
    memory = list(initial)
    reads, addresses, incoming = [], [], {}
    touched = set()
    for op, offset in program:
        address = (offset + (controller if op == "indexed" else 0)) % len(memory)
        if op == "store":
            memory[address] = controller
            reads.append(2)  # empty read token
            addresses.append(None)
        else:
            value = memory[address]
            if address not in touched:
                incoming[address] = value
            controller ^= value
            reads.append(value)
            addresses.append(address)
        touched.add(address)
    return controller, tuple(reads), addresses, incoming


def check_local():
    # Complete instruction choices for three steps, all eight entry memories.
    ops = list(product(("direct", "indexed", "store"), range(3)))
    memories = list(product(range(2), repeat=3))
    sites = blocks = kept = repairs = 0
    for prog in product(ops, repeat=3):
        for ctrl in (0, 1):
            rows = [run_block(prog, x, ctrl) for x in memories]
            entries_by_word = defaultdict(list)
            for entry, (_, word, _, _) in zip(memories, rows):
                entries_by_word[word].append(entry)
            for base, (out, word, addresses, _) in zip(memories, rows):
                # Choose the real exit controller. Different entries may generate the same string.
                groups = defaultdict(set)
                for end, other, _, incoming in rows:
                    if end == out:
                        forced = sum(base[a] != value for a, value in incoming.items())
                        nearest = min(sum(x != y for x, y in zip(base, entry))
                                      for entry in entries_by_word[other])
                        assert nearest == forced
                        repairs += 1
                    if end == out and distance(word, other) > 1:
                        first = next(i for i in range(len(word)) if word[i] != other[i])
                        a = addresses[first]
                        assert a is not None
                        groups[a].add(other)
                for entry, (end, other, _, _) in zip(memories, rows):
                    if end == out and all(entry[a] == base[a] for a in groups):
                        assert distance(word, other) <= 1
                        kept += 1
                sites += len(groups)
                blocks += 1
    return blocks, sites, kept, repairs


def toeplitz(seed, value, b, width):
    # Logical column j sits at bit b-1-j of value and uses diagonal seed bit i+b-1-j.
    return sum(((value & ((seed >> i) & ((1 << b)-1))).bit_count() % 2) << i
               for i in range(width))


def check_tags():
    tests = 0
    for b in range(1, 7):
        for width in range(1, b+1):
            seeds = range(1 << (b+width-1))
            for diff in range(1, 1 << b):
                counts = [0] * (1 << width)
                for seed in seeds:
                    counts[toeplitz(seed, diff, b, width)] += 1
                assert counts == [1 << (b-1)] * len(counts)
                tests += 1
    # Two menus use the same seed, each with two competitors against its honest member.
    cases = 0
    b, width = 5, 3
    for a in range(1, 10):
        for c in range(1, 10):
            differences = {a, a+1, c, c+1}
            good = sum(all(toeplitz(seed, e, b, width) for e in differences)
                       for seed in range(1 << (b+width-1)))
            assert 2*good >= 1 << (b+width-1)
            cases += 1
    return tests, cases


if __name__ == "__main__":
    blocks, sites, kept, repairs = check_local()
    print(f"{blocks} genuine block cases, {sites} far first-departure address groups, "
          f"{kept} protected near paths counting initial memories, {repairs} minimum repairs")
    tags, shared = check_tags()
    print(f"{tags} complete difference/width histograms, {shared} common-seed cases")
