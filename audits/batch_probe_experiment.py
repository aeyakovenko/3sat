"""Exhaust all local proof-header maps on four-bit input domains."""
from fractions import Fraction
from itertools import combinations, product


def marked_flips(fiber, masks, width):
    if not fiber:
        return 0
    seen = {mask: {x & mask for x in fiber} for mask in masks}
    return sum(any((y & mask) not in observed for mask, observed in seen.items())
               for x in fiber for bit in range(width) for y in [x ^ (1 << bit)])


def experiment(domain, kind):
    width = 4
    for probes in (1, 2):
        masks = [sum(1 << bit for bit in subset)
                 for subset in combinations(range(width), probes)]
        marks = {subset: marked_flips([x for i, x in enumerate(domain)
                                       if subset & (1 << i)], masks, width)
                 for subset in range(1 << len(domain))}
        for header_bits in (0, 1, 2):
            # Two header bits and eight even strings give 65,536 maps.
            colors = 1 << header_bits
            best = 0
            for labeling in product(range(colors), repeat=len(domain)):
                fibers = [0] * colors
                for i, color in enumerate(labeling):
                    fibers[color] |= 1 << i
                best = max(best, sum(marks[fiber] for fiber in fibers))
            average = Fraction(best, len(domain))
            if kind == "slice":
                assert average * (width - 2 * (probes - 1)) <= 2 * width * probes * header_bits
            else:
                assert average * (width - probes) <= width * probes * header_bits
            print(f"{kind}: q={probes}, h={header_bits}, maximum mean marked flips={average}")


if __name__ == "__main__":
    experiment([x for x in range(16) if x.bit_count() % 2 == 0], "parity")
    experiment([x for x in range(16) if x.bit_count() == 2], "slice")
