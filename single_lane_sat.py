"""Compile two-path 3-colorability into a single permuted parity lane."""

from itertools import pairwise

from simple_permutation_successor import valid_order

TIPS = (1, 4, 3, 5, 6, 0, 2)


ANCHOR = (16, 8, 5, 3, 13, 4, 2, 10, 17, 15, 0, 9, 11, 6, 12, 7, 14, 1)
RED_GAP = (13, 14)
BLUE_GAPS = ((8, 5), (15, 0))


def site(j):
    """Red rank of strip vertex x_j, where strip subscripts start at one."""
    return RED_GAP[0] + j


def render_lists(m, odd, even):
    """Place two supplied lists of red ranks in the designated blue gaps."""
    out = []
    for anchor_vertex in ANCHOR:
        out.append(anchor_vertex + m * (anchor_vertex > RED_GAP[0]))
        if anchor_vertex == BLUE_GAPS[0][0]:
            out.extend(odd)
        elif anchor_vertex == BLUE_GAPS[1][0]:
            out.extend(even)
    return tuple(out)


def compile_lane(source):
    """Return a simple permutation in its packed-order mathematical representation."""
    if not valid_order(source):
        raise ValueError("expected distinct ranks 0 through n-1")
    tiles = len(source) + 6
    blue = (0, 1, 2, *(3 + i for i in source), tiles - 3, tiles - 2, tiles - 1)
    total = 14 * tiles + 1
    fixed = [site(i) for i in range(1, total + 1, 2)]
    scrambled = [site(2 + 2 * (7 * t + j)) for t in blue for j in TIPS]
    return render_lists(total, fixed, scrambled)


def extend_coloring(source, colors, anchor):
    """Extend a supplied proper source coloring to the full rendered instance."""

    def avoid(*forbidden):
        return next(x for x in range(3) if x not in forbidden)

    if colors:
        prefix_end = avoid(colors[0], colors[source[0]])
        suffix_start = avoid(colors[-1], colors[source[-1]])
        tile_colors = [
            0,
            avoid(0, prefix_end),
            prefix_end,
            *colors,
            suffix_start,
            avoid(0, suffix_start),
            0,
        ]
    else:
        tile_colors = [0, 1, 2, 1, 2, 0]
    # The final y-port has no corresponding source vertex.
    strip = []
    for a, b in pairwise(tile_colors + [2]):
        assert a != b
        d = avoid(a, b)
        bases = (a, b, d, b, d, a, d)
        tips = (d, a, a, a, b, b, a)
        for y, z in zip(bases, tips):
            strip.extend((y, z))
    strip.append(2)
    return anchor[: RED_GAP[1]] + tuple(strip) + anchor[RED_GAP[1] :]
