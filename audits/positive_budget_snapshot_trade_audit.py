"""Verify exact stage costs for the 1100100 true-start snapshot trade."""

from fractions import Fraction as F


def stage_costs(c, e, d, h, x, y, z):
    """Use separate guessed, incoming, and outgoing sizes at each slowdown."""
    root_code, root_lookup = e / c, d / c
    assert c >= 1 and min(e, d, h, x, y, z) >= 0
    assert 1 - x >= h and 1 - x - y >= h

    first_list = x + root_code
    second_list = y + root_code
    outer_input = max(h, first_list)
    inner_list_input = max(h, root_code, second_list)
    first_leaf_input = max(h, root_code)
    first_leaf_time = 1 - x - y + root_lookup
    # The challenge index and observation require only logarithmically many bits.
    u1 = max(0, inner_list_input, first_leaf_input, first_leaf_time)
    u2 = max(second_list, outer_input, inner_list_input, c * u1)

    fresh_time, fresh_code, fresh_lookup = c * u2, e * u2, d * u2
    assert fresh_time - z >= h
    fresh_list = z + fresh_code
    merged_guess = max(first_list, fresh_list)
    merged_output = max(outer_input, fresh_list)
    second_leaf_input = max(outer_input, fresh_code)
    second_leaf_time = fresh_time - z + fresh_lookup
    u3 = max(0, merged_output, second_leaf_input, second_leaf_time)
    u4 = max(merged_guess, h, merged_output, c * u3)

    assert u1 == max(h, y + root_code, 1 - x - y + root_lookup)
    assert u2 == max(h, x + root_code, c * u1)
    assert u3 == max(h, x + root_code, z + fresh_code, (c + d) * u2 - z)
    assert c * u4 == c**2 * u3
    return u1, u2, c * u4


def main():
    examples = [
        (F(3, 2), F(1, 13), ".39", ".305", ".4",
         F(2779, 7800), F(2779, 5200), F(538731, 540800)),
        (F(8, 5), F(1, 3000), ".3904", ".3048", ".3904",
         F(36601, 120000), F(36601, 75000), F(46873, 46875)),
    ]
    for c, budget, x, y, z, u1, u2, final in examples:
        actual = stage_costs(c, budget, budget, F(1, 10), F(x), F(y), F(z))
        assert actual == (u1, u2, final) and final < 1
        print(f"c={c}  e=d={budget}  final ratio={final}  gap={1-final}")

    for numerator in range(100, 201):
        c = F(numerator, 100)
        x = c**2 / (4 + c**2)
        y = (1 - x) / 2
        result = stage_costs(c, 0, 0, F(1, 10), x, y, x)
        assert result[-1] == c**4 / (4 + c**2)
    print("Verified the zero-budget specialization at 101 rational exponents.")


if __name__ == "__main__":
    main()
