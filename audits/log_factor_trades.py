"""Check the finite packed-RAM logarithmic-exponent calculation exactly."""

from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class Profile:
    work: Fraction
    public: Fraction


def trade(time_loss, space_saving, prior, depth, *, direct_leaf=False):
    """Choose the cuts, then recompute costs from the innermost replay out."""
    e, f = prior.work, prior.public
    assert depth >= 1 and e >= 0
    if direct_leaf:
        assert depth == 1
    else:
        assert e <= f

    new_public = f + (depth - 1) * e
    balanced = (time_loss + depth * (f - space_saving)
                + Fraction(depth * (depth + 1), 2) * e) / (depth + 1)
    target = max(balanced, new_public - space_saving)
    widths = [target + space_saving - f - i * e for i in range(depth)]
    assert min(widths) >= 0

    # Load the selected endpoints and replay the last segment. Each enclosing
    # elimination charges all its own checkpoints as public input. Outer
    # levels also multiply the previous pure input bill by the work loss.
    work = max(time_loss - sum(widths), -space_saving)
    input_exponent = None
    for width in reversed(widths):
        work = max(work + e, width - space_saving + f)
        input_exponent = (f if input_exponent is None
                          else max(f, input_exponent + e))
    assert work == target
    assert input_exponent == new_public
    return Profile(work, new_public)


def main():
    a, b = Fraction(0), Fraction(25, 4)
    time_loss, direct_input, space_saving = a + 3, a + 2, b - 2
    profile = Profile(time_loss, direct_input)
    for i in range(6):
        profile = trade(time_loss, space_saving, profile, 1, direct_leaf=(i == 0))
        assert 0 <= profile.work <= profile.public
    assert profile == Profile(Fraction(201, 256), direct_input)
    print(f"Six one-level cuts: e={profile.work}, f={profile.public}")

    exact_two = trade(time_loss, space_saving, profile, 2)
    exact_four = trade(time_loss, space_saving, exact_two, 4)
    assert exact_four == Profile(Fraction(-1, 640), Fraction(233, 64))

    rounded = Fraction(51, 64)
    assert profile.work <= rounded <= profile.public
    profile = Profile(rounded, profile.public)
    expected = [
        (2, Fraction(19, 64), Fraction(179, 64)),
        (4, Fraction(1, 32), Fraction(59, 16)),
        (11, Fraction(-3, 32), Fraction(4)),
    ]
    for depth, work, public in expected:
        profile = trade(time_loss, space_saving, profile, depth)
        assert profile == Profile(work, public)
        print(f"Depth {depth}: e={profile.work}, f={profile.public}")
    assert profile.work < 0
    print(f"Without rounding, depths 2 and 4 end at e={exact_four.work}.")


if __name__ == "__main__":
    main()
