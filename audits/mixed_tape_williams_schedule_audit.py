"""Exact exponent checks for the finite mixed-tape alternation schedule."""

from fractions import Fraction as F


def at_most(actual, ceiling):
    assert actual <= ceiling, (actual, ceiling)
    return actual


def cube(clock, dimension, scratch):
    """Cap crossing records at exponent 1. Return residual simulator space."""
    side = (1 + scratch) * clock - 1
    assert scratch * clock <= side <= clock
    assert clock - side + scratch * clock == 1
    return max(dimension * side, scratch * clock)


def checkpoints(clock, space, split, previous_public):
    """A full table, two selected configurations and one replay."""
    assert 0 <= split <= clock
    assert space <= clock - split
    chart = space + split
    pair_public = max(previous_public, space)
    return chart, pair_public, clock - split


def shortcut(dimension, scratch, slowdown, levels):
    denominator = dimension + 1 + dimension * scratch
    clock = F(dimension + 2) / denominator
    clocks = []
    for level in range(levels):
        space = cube(clock, dimension, scratch)
        chart, public, replay = checkpoints(clock, space, 1 - space, F(1))
        at_most(chart, 1)
        at_most(public, 1)
        if level == 0:
            at_most(replay, 1)
        else:
            at_most(slowdown * max(1, public, replay), clocks[-1])
        clocks.append(clock)
        clock = (dimension + 1 + clock / slowdown) / denominator
    return clocks


def boundary_polynomial(dimension, scratch, exponent):
    mixed = dimension + 1 + dimension * scratch
    return (((2 * mixed - 1) * exponent**2 - 1) * exponent * (mixed * exponent - 1)**2
            - (2 * dimension + 1) * (dimension + 1) * (mixed * exponent - 1)
            - (dimension + 1)**2)


def main():
    dimension = 2
    scratch = F(1, 4)
    slowdown = F(541, 500)
    start = F(59, 50)
    outer_public = F(1007, 1000)
    assert (dimension + 1 + dimension * scratch) * slowdown**2 > slowdown + dimension + 1
    clocks = shortcut(dimension, scratch, slowdown, 3)
    space = cube(start, dimension, scratch)
    assert space == F(19, 20)
    first_split = outer_public - space
    chart, selected_public, segment = checkpoints(start, space, first_split, F(1))
    assert chart == outer_public
    assert 1 <= outer_public <= slowdown
    assert selected_public == 1
    chart, selected_public, replay = checkpoints(segment, space, 1 - space, selected_public)
    assert chart == selected_public == 1
    first_hybrid = slowdown * max(1, selected_public, replay)
    assert first_hybrid < clocks[-1]

    # The first shortcut has public exponent 1. Remove the short existential,
    # then the full universal; the latter receives the first outer table.
    remove_short = slowdown * max(F(1), F(1))
    second_hybrid = slowdown * max(outer_public, F(1), remove_short)
    assert second_hybrid == slowdown**2
    assert second_hybrid < outer_public * clocks[-1]

    # The second shortcut works at scale n**outer_public, so the retained
    # original input and both supplied configurations all fit that exponent.
    remove_last_short = slowdown * outer_public
    finish = slowdown * max(F(1), outer_public, remove_last_short)
    assert finish < start
    lower_root = F(1082755, 10**6)
    upper_root = F(1082756, 10**6)
    assert boundary_polynomial(dimension, scratch, lower_root) < 0
    assert boundary_polynomial(dimension, scratch, upper_root) > 0
    # Six evaluations determine any degree-five polynomial. Compare the
    # zero-scratch specialization with the published quintic for six d values.
    for d in range(1, 7):
        for x in range(6):
            old = ((2*d+1)*(d+1)**2*x**5 - 2*(d+1)*(2*d+1)*x**4
                   - d**2*x**3 + 2*(d+1)*x**2 - ((2*d+1)*(d+1)**2+1)*x + d*(d+1))
            assert boundary_polynomial(d, 0, x) == old
    print('root bracket:', lower_root, upper_root)
    print('shortcut clocks:', *(str(value) for value in clocks))
    print('first shortcut:', first_hybrid, '<', clocks[-1])
    print('second shortcut:', second_hybrid, '<', outer_public * clocks[-1])
    print('hierarchy:', finish, '<', start)


if __name__ == '__main__':
    main()
