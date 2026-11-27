"""Check the five-stage rational exponent certificate in live-value-replay.md."""

from fractions import Fraction

EXPONENT = Fraction(6811, 5000)
HORIZON = Fraction(97, 100)
STAGES = (20, 25, 27, 30, 1)


def round_up(value: Fraction, scale: int = 10**9) -> Fraction:
    return Fraction(-(-value.numerator * scale // value.denominator), scale)


def certify() -> None:
    inner_work = public = EXPONENT
    widest = Fraction(0)
    for stage, count in enumerate(STAGES, start=1):
        outer_work = inner_work
        public = round_up(public * inner_work)
        for _ in range(count):
            assert 1 <= outer_work <= inner_work <= public
            cut = public * EXPONENT / (public + inner_work * outer_work)
            assert 0 < cut < HORIZON
            widest = max(widest, cut)
            updated = round_up(inner_work * outer_work * cut)
            assert updated >= public * (EXPONENT - cut)
            assert updated < outer_work
            outer_work = updated
        inner_work = outer_work
        print(f"stage {stage}: work {float(inner_work):.9f}, public {float(public):.9f}")
    assert inner_work < 1
    print(f"{sum(STAGES)} transformations; largest cut exponent {float(widest):.9f}")


if __name__ == "__main__":
    certify()
